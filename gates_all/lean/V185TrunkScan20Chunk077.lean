import V185TrunkScan20Chunk076

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_469079 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_469079 : Nat := 118140960795 + 469079 * 2 ^ 59
def prefixEnd_469079 : Nat := 4983230072969 + 3 ^ 40 * 469079 * 2
def baseEnd_469079 : Nat := 214100437271533742182445

theorem tailTrace_469079 : CollatzResearch.WordTrace tailWord_469079 prefixEnd_469079 214100437271533742182445 := by
  unfold tailWord_469079
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108716667614370160242291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11405811111742913440161527 17108716667614370160242291)
  ·
    refine ⟨25663075001421555240363437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17108716667614370160242291 25663075001421555240363437)
    ·
      refine ⟨9623653125533083215136289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25663075001421555240363437 9623653125533083215136289)
      ·
        refine ⟨7217739844149812411352217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9623653125533083215136289 7217739844149812411352217)
        ·
          refine ⟨5413304883112359308514163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7217739844149812411352217 5413304883112359308514163)
          ·
            refine ⟨8119957324668538962771245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413304883112359308514163 8119957324668538962771245)
            ·
              refine ⟨3044983996750702111039217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8119957324668538962771245 3044983996750702111039217)
              ·
                refine ⟨2283737997563026583279413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3044983996750702111039217 2283737997563026583279413)
                ·
                  refine ⟨214100437271533742182445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2283737997563026583279413 214100437271533742182445)
                  ·
                    rfl

theorem cell20_469079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_469079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469079 prefixEnd_469079 := by exact prefixLift 469079
  have htrace : WordTrace (prefixWord ++ tailWord_469079) baseStart_469079 baseEnd_469079 := by
    simpa [prefixWord, tailWord_469079, baseEnd_469079] using wordTrace_append hprefix tailTrace_469079
  have hstable : (prefixWord ++ tailWord_469079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469079).length < 2 ^ (prefixWord ++ tailWord_469079).sum := by decide
  have hdescent : baseEnd_469079 < baseStart_469079 := by decide
  rcases family_descends (prefixWord ++ tailWord_469079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469103 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_469103 : Nat := 118140960795 + 469103 * 2 ^ 59
def prefixEnd_469103 : Nat := 4983230072969 + 3 ^ 40 * 469103 * 2
def baseEnd_469103 : Nat := 214111391525496325382347

theorem tailTrace_469103 : CollatzResearch.WordTrace tailWord_469103 prefixEnd_469103 214111391525496325382347 := by
  unfold tailWord_469103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109592019527422259115963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11406394679684948172743975 17109592019527422259115963)
  ·
    refine ⟨25664388029291133388673945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17109592019527422259115963 25664388029291133388673945)
    ·
      refine ⟨19248291021968350041505459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25664388029291133388673945 19248291021968350041505459)
      ·
        refine ⟨28872436532952525062258189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19248291021968350041505459 28872436532952525062258189)
        ·
          refine ⟨10827163699857196898346821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28872436532952525062258189 10827163699857196898346821)
          ·
            refine ⟨2030093193723224418440029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10827163699857196898346821 2030093193723224418440029)
            ·
              refine ⟨761284947646209156915011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030093193723224418440029 761284947646209156915011)
              ·
                refine ⟨1141927421469313735372517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761284947646209156915011 1141927421469313735372517)
                ·
                  refine ⟨214111391525496325382347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141927421469313735372517 214111391525496325382347)
                  ·
                    rfl

theorem cell20_469103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_469103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469103 prefixEnd_469103 := by exact prefixLift 469103
  have htrace : WordTrace (prefixWord ++ tailWord_469103) baseStart_469103 baseEnd_469103 := by
    simpa [prefixWord, tailWord_469103, baseEnd_469103] using wordTrace_append hprefix tailTrace_469103
  have hstable : (prefixWord ++ tailWord_469103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469103).length < 2 ^ (prefixWord ++ tailWord_469103).sum := by decide
  have hdescent : baseEnd_469103 < baseStart_469103 := by decide
  rcases family_descends (prefixWord ++ tailWord_469103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469113 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 3]
def baseStart_469113 : Nat := 118140960795 + 469113 * 2 ^ 59
def prefixEnd_469113 : Nat := 4983230072969 + 3 ^ 40 * 469113 * 2
def baseEnd_469113 : Nat := 214115955797980735048973

theorem tailTrace_469113 : CollatzResearch.WordTrace tailWord_469113 prefixEnd_469113 214115955797980735048973 := by
  unfold tailWord_469113
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109956749491193966979993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11406637832994129311319995 17109956749491193966979993)
  ·
    refine ⟨12832467562118395475234995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17109956749491193966979993 12832467562118395475234995)
    ·
      refine ⟨19248701343177593212852493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832467562118395475234995 19248701343177593212852493)
      ·
        refine ⟨7218263003691597454819685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19248701343177593212852493 7218263003691597454819685)
        ·
          refine ⟨1353424313192174522778691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7218263003691597454819685 1353424313192174522778691)
          ·
            refine ⟨2030136469788261784168037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353424313192174522778691 2030136469788261784168037)
            ·
              refine ⟨380650588085299084531507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2030136469788261784168037 380650588085299084531507)
              ·
                refine ⟨570975882127948626797261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380650588085299084531507 570975882127948626797261)
                ·
                  refine ⟨214115955797980735048973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570975882127948626797261 214115955797980735048973)
                  ·
                    rfl

theorem cell20_469113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_469113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469113 prefixEnd_469113 := by exact prefixLift 469113
  have htrace : WordTrace (prefixWord ++ tailWord_469113) baseStart_469113 baseEnd_469113 := by
    simpa [prefixWord, tailWord_469113, baseEnd_469113] using wordTrace_append hprefix tailTrace_469113
  have hstable : (prefixWord ++ tailWord_469113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469113).length < 2 ^ (prefixWord ++ tailWord_469113).sum := by decide
  have hdescent : baseEnd_469113 < baseStart_469113 := by decide
  rcases family_descends (prefixWord ++ tailWord_469113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469150 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_469150 : Nat := 118140960795 + 469150 * 2 ^ 59
def prefixEnd_469150 : Nat := 4983230072969 + 3 ^ 40 * 469150 * 2
def baseEnd_469150 : Nat := 214132843606173050815489

theorem tailTrace_469150 : CollatzResearch.WordTrace tailWord_469150 prefixEnd_469150 214132843606173050815489 := by
  unfold tailWord_469150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138913281294643660759613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11407537500238099524051269 2138913281294643660759613)
  ·
    refine ⟨802092480485491372784855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2138913281294643660759613 802092480485491372784855)
    ·
      refine ⟨1203138720728237059177283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802092480485491372784855 1203138720728237059177283)
      ·
        refine ⟨1804708081092355588765925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203138720728237059177283 1804708081092355588765925)
        ·
          refine ⟨338382765204816672893611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1804708081092355588765925 338382765204816672893611)
          ·
            refine ⟨507574147807225009340417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338382765204816672893611 507574147807225009340417)
            ·
              refine ⟨380680610855418757005313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507574147807225009340417 380680610855418757005313)
              ·
                refine ⟨285510458141564067753985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380680610855418757005313 285510458141564067753985)
                ·
                  refine ⟨214132843606173050815489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285510458141564067753985 214132843606173050815489)
                  ·
                    rfl

theorem cell20_469150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_469150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469150 prefixEnd_469150 := by exact prefixLift 469150
  have htrace : WordTrace (prefixWord ++ tailWord_469150) baseStart_469150 baseEnd_469150 := by
    simpa [prefixWord, tailWord_469150, baseEnd_469150] using wordTrace_append hprefix tailTrace_469150
  have hstable : (prefixWord ++ tailWord_469150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469150).length < 2 ^ (prefixWord ++ tailWord_469150).sum := by decide
  have hdescent : baseEnd_469150 < baseStart_469150 := by decide
  rcases family_descends (prefixWord ++ tailWord_469150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469151 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_469151 : Nat := 118140960795 + 469151 * 2 ^ 59
def prefixEnd_469151 : Nat := 4983230072969 + 3 ^ 40 * 469151 * 2
def baseEnd_469151 : Nat := 214133300033421491782151

theorem tailTrace_469151 : CollatzResearch.WordTrace tailWord_469151 prefixEnd_469151 214133300033421491782151 := by
  unfold tailWord_469151
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111342723353526456863307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11407561815569017637908871 17111342723353526456863307)
  ·
    refine ⟨25667014085030289685294961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17111342723353526456863307 25667014085030289685294961)
    ·
      refine ⟨19250260563772717263971221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25667014085030289685294961 19250260563772717263971221)
      ·
        refine ⟨902355963926846121748651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19250260563772717263971221 902355963926846121748651)
        ·
          refine ⟨1353533945890269182622977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902355963926846121748651 1353533945890269182622977)
          ·
            refine ⟨1015150459417701886967233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353533945890269182622977 1015150459417701886967233)
            ·
              refine ⟨761362844563276415225425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015150459417701886967233 761362844563276415225425)
              ·
                refine ⟨571022133422457311419069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761362844563276415225425 571022133422457311419069)
                ·
                  refine ⟨214133300033421491782151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571022133422457311419069 214133300033421491782151)
                  ·
                    rfl

theorem cell20_469151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_469151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469151 prefixEnd_469151 := by exact prefixLift 469151
  have htrace : WordTrace (prefixWord ++ tailWord_469151) baseStart_469151 baseEnd_469151 := by
    simpa [prefixWord, tailWord_469151, baseEnd_469151] using wordTrace_append hprefix tailTrace_469151
  have hstable : (prefixWord ++ tailWord_469151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469151).length < 2 ^ (prefixWord ++ tailWord_469151).sum := by decide
  have hdescent : baseEnd_469151 < baseStart_469151 := by decide
  rcases family_descends (prefixWord ++ tailWord_469151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469154 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_469154 : Nat := 118140960795 + 469154 * 2 ^ 59
def prefixEnd_469154 : Nat := 4983230072969 + 3 ^ 40 * 469154 * 2
def baseEnd_469154 : Nat := 214134669315166814682139

theorem tailTrace_469154 : CollatzResearch.WordTrace tailWord_469154 prefixEnd_469154 214134669315166814682139 := by
  unfold tailWord_469154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277863035585664492305629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11407634761561771979481677 4277863035585664492305629)
  ·
    refine ⟨1604198638344624184614611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4277863035585664492305629 1604198638344624184614611)
    ·
      refine ⟨2406297957516936276921917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604198638344624184614611 2406297957516936276921917)
      ·
        refine ⟨902361734068851103845719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2406297957516936276921917 902361734068851103845719)
        ·
          refine ⟨1353542601103276655768579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902361734068851103845719 1353542601103276655768579)
          ·
            refine ⟨2030313901654914983652869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353542601103276655768579 2030313901654914983652869)
            ·
              refine ⟨380683856560296559434913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2030313901654914983652869 380683856560296559434913)
              ·
                refine ⟨285512892420222419576185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380683856560296559434913 285512892420222419576185)
                ·
                  refine ⟨214134669315166814682139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285512892420222419576185 214134669315166814682139)
                  ·
                    rfl

theorem cell20_469154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_469154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469154 prefixEnd_469154 := by exact prefixLift 469154
  have htrace : WordTrace (prefixWord ++ tailWord_469154) baseStart_469154 baseEnd_469154 := by
    simpa [prefixWord, tailWord_469154, baseEnd_469154] using wordTrace_append hprefix tailTrace_469154
  have hstable : (prefixWord ++ tailWord_469154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469154).length < 2 ^ (prefixWord ++ tailWord_469154).sum := by decide
  have hdescent : baseEnd_469154 < baseStart_469154 := by decide
  rcases family_descends (prefixWord ++ tailWord_469154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469165 : List Nat := [1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_469165 : Nat := 118140960795 + 469165 * 2 ^ 59
def prefixEnd_469165 : Nat := 4983230072969 + 3 ^ 40 * 469165 * 2
def baseEnd_469165 : Nat := 71379896671633221771809

theorem tailTrace_469165 : CollatzResearch.WordTrace tailWord_469165 prefixEnd_469165 71379896671633221771809 := by
  unfold tailWord_469165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111853345302806847872949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11407902230201871231915299 17111853345302806847872949)
  ·
    refine ⟨1604236251122138141988089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17111853345302806847872949 1604236251122138141988089)
    ·
      refine ⟨1203177188341603606491067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1604236251122138141988089 1203177188341603606491067)
      ·
        refine ⟨1804765782512405409736601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203177188341603606491067 1804765782512405409736601)
        ·
          refine ⟨1353574336884304057302451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1804765782512405409736601 1353574336884304057302451)
          ·
            refine ⟨2030361505326456085953677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353574336884304057302451 2030361505326456085953677)
            ·
              refine ⟨761385564497421032232629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030361505326456085953677 761385564497421032232629)
              ·
                refine ⟨71379896671633221771809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 761385564497421032232629 71379896671633221771809)
                ·
                  rfl

theorem cell20_469165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_469165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469165 prefixEnd_469165 := by exact prefixLift 469165
  have htrace : WordTrace (prefixWord ++ tailWord_469165) baseStart_469165 baseEnd_469165 := by
    simpa [prefixWord, tailWord_469165, baseEnd_469165] using wordTrace_append hprefix tailTrace_469165
  have hstable : (prefixWord ++ tailWord_469165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469165).length < 2 ^ (prefixWord ++ tailWord_469165).sum := by decide
  have hdescent : baseEnd_469165 < baseStart_469165 := by decide
  rcases family_descends (prefixWord ++ tailWord_469165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469182 : List Nat := [4, 2, 1, 1, 4, 1, 3, 4]
def baseStart_469182 : Nat := 118140960795 + 469182 * 2 ^ 59
def prefixEnd_469182 : Nat := 4983230072969 + 3 ^ 40 * 469182 * 2
def baseEnd_469182 : Nat := 71382483092707720582897

theorem tailTrace_469182 : CollatzResearch.WordTrace tailWord_469182 prefixEnd_469182 71382483092707720582897 := by
  unfold tailWord_469182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139059173280152343905225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11408315590827479167494533 2139059173280152343905225)
  ·
    refine ⟨1604294379960114257928919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2139059173280152343905225 1604294379960114257928919)
    ·
      refine ⟨2406441569940171386893379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604294379960114257928919 2406441569940171386893379)
      ·
        refine ⟨3609662354910257080340069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406441569940171386893379 3609662354910257080340069)
        ·
          refine ⟨676811691545673202563763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3609662354910257080340069 676811691545673202563763)
          ·
            refine ⟨1015217537318509803845645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676811691545673202563763 1015217537318509803845645)
            ·
              refine ⟨380706576494441176442117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015217537318509803845645 380706576494441176442117)
              ·
                refine ⟨71382483092707720582897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380706576494441176442117 71382483092707720582897)
                ·
                  rfl

theorem cell20_469182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_469182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469182 prefixEnd_469182 := by exact prefixLift 469182
  have htrace : WordTrace (prefixWord ++ tailWord_469182) baseStart_469182 baseEnd_469182 := by
    simpa [prefixWord, tailWord_469182, baseEnd_469182] using wordTrace_append hprefix tailTrace_469182
  have hstable : (prefixWord ++ tailWord_469182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469182).length < 2 ^ (prefixWord ++ tailWord_469182).sum := by decide
  have hdescent : baseEnd_469182 < baseStart_469182 := by decide
  rcases family_descends (prefixWord ++ tailWord_469182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469206 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_469206 : Nat := 118140960795 + 469206 * 2 ^ 59
def prefixEnd_469206 : Nat := 4983230072969 + 3 ^ 40 * 469206 * 2
def baseEnd_469206 : Nat := 214158403532085744948593

theorem tailTrace_469206 : CollatzResearch.WordTrace tailWord_469206 prefixEnd_469206 214158403532085744948593 := by
  unfold tailWord_469206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069584296134641928132217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11408899158769513900076981 1069584296134641928132217)
  ·
    refine ⟨802188222100981446099163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1069584296134641928132217 802188222100981446099163)
    ·
      refine ⟨1203282333151472169148745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802188222100981446099163 1203282333151472169148745)
      ·
        refine ⟨902461749863604126861559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1203282333151472169148745 902461749863604126861559)
        ·
          refine ⟨1353692624795406190292339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902461749863604126861559 1353692624795406190292339)
          ·
            refine ⟨2030538937193109285438509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353692624795406190292339 2030538937193109285438509)
            ·
              refine ⟨761452101447415982039441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030538937193109285438509 761452101447415982039441)
              ·
                refine ⟨571089076085561986529581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761452101447415982039441 571089076085561986529581)
                ·
                  refine ⟨214158403532085744948593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571089076085561986529581 214158403532085744948593)
                  ·
                    rfl

theorem cell20_469206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_469206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469206 prefixEnd_469206 := by exact prefixLift 469206
  have htrace : WordTrace (prefixWord ++ tailWord_469206) baseStart_469206 baseEnd_469206 := by
    simpa [prefixWord, tailWord_469206, baseEnd_469206] using wordTrace_append hprefix tailTrace_469206
  have hstable : (prefixWord ++ tailWord_469206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469206).length < 2 ^ (prefixWord ++ tailWord_469206).sum := by decide
  have hdescent : baseEnd_469206 < baseStart_469206 := by decide
  rcases family_descends (prefixWord ++ tailWord_469206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469210 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_469210 : Nat := 118140960795 + 469210 * 2 ^ 59
def prefixEnd_469210 : Nat := 4983230072969 + 3 ^ 40 * 469210 * 2
def baseEnd_469210 : Nat := 214160229241079508815243

theorem tailTrace_469210 : CollatzResearch.WordTrace tailWord_469210 prefixEnd_469210 214160229241079508815243 := by
  unfold tailWord_469210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278373657534944883315271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11408996420093186355507389 4278373657534944883315271)
  ·
    refine ⟨6417560486302417324972907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4278373657534944883315271 6417560486302417324972907)
    ·
      refine ⟨9626340729453625987459361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417560486302417324972907 9626340729453625987459361)
      ·
        refine ⟨7219755547090219490594521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9626340729453625987459361 7219755547090219490594521)
        ·
          refine ⟨5414816660317664617945891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7219755547090219490594521 5414816660317664617945891)
          ·
            refine ⟨8122224990476496926918837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414816660317664617945891 8122224990476496926918837)
            ·
              refine ⟨761458592857171586898641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8122224990476496926918837 761458592857171586898641)
              ·
                refine ⟨571093944642878690173981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761458592857171586898641 571093944642878690173981)
                ·
                  refine ⟨214160229241079508815243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571093944642878690173981 214160229241079508815243)
                  ·
                    rfl

theorem cell20_469210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_469210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469210 prefixEnd_469210 := by exact prefixLift 469210
  have htrace : WordTrace (prefixWord ++ tailWord_469210) baseStart_469210 baseEnd_469210 := by
    simpa [prefixWord, tailWord_469210, baseEnd_469210] using wordTrace_append hprefix tailTrace_469210
  have hstable : (prefixWord ++ tailWord_469210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469210).length < 2 ^ (prefixWord ++ tailWord_469210).sum := by decide
  have hdescent : baseEnd_469210 < baseStart_469210 := by decide
  rcases family_descends (prefixWord ++ tailWord_469210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469213 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 2]
def baseStart_469213 : Nat := 118140960795 + 469213 * 2 ^ 59
def prefixEnd_469213 : Nat := 4983230072969 + 3 ^ 40 * 469213 * 2
def baseEnd_469213 : Nat := 214161598522824831715231

theorem tailTrace_469213 : CollatzResearch.WordTrace tailWord_469213 prefixEnd_469213 214161598522824831715231 := by
  unfold tailWord_469213
  simp only [CollatzResearch.WordTrace]
  refine ⟨17113604049128911045620293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11409069366085940697080195 17113604049128911045620293)
  ·
    refine ⟨3208800759211670821053805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17113604049128911045620293 3208800759211670821053805)
    ·
      refine ⟨1203300284704376557895177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3208800759211670821053805 1203300284704376557895177)
      ·
        refine ⟨902475213528282418421383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1203300284704376557895177 902475213528282418421383)
        ·
          refine ⟨1353712820292423627632075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902475213528282418421383 1353712820292423627632075)
          ·
            refine ⟨2030569230438635441448113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353712820292423627632075 2030569230438635441448113)
            ·
              refine ⟨1522926922828976581086085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030569230438635441448113 1522926922828976581086085)
              ·
                refine ⟨285548798030433108953641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1522926922828976581086085 285548798030433108953641)
                ·
                  refine ⟨214161598522824831715231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285548798030433108953641 214161598522824831715231)
                  ·
                    rfl

theorem cell20_469213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_469213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469213 prefixEnd_469213 := by exact prefixLift 469213
  have htrace : WordTrace (prefixWord ++ tailWord_469213) baseStart_469213 baseEnd_469213 := by
    simpa [prefixWord, tailWord_469213, baseEnd_469213] using wordTrace_append hprefix tailTrace_469213
  have hstable : (prefixWord ++ tailWord_469213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469213).length < 2 ^ (prefixWord ++ tailWord_469213).sum := by decide
  have hdescent : baseEnd_469213 < baseStart_469213 := by decide
  rcases family_descends (prefixWord ++ tailWord_469213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469217 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_469217 : Nat := 118140960795 + 469217 * 2 ^ 59
def prefixEnd_469217 : Nat := 4983230072969 + 3 ^ 40 * 469217 * 2
def baseEnd_469217 : Nat := 214163424231818595581881

theorem tailTrace_469217 : CollatzResearch.WordTrace tailWord_469217 prefixEnd_469217 214163424231818595581881 := by
  unfold tailWord_469217
  simp only [CollatzResearch.WordTrace]
  refine ⟨17113749941114419728765905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11409166627409613152510603 17113749941114419728765905)
  ·
    refine ⟨12835312455835814796574429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17113749941114419728765905 12835312455835814796574429)
    ·
      refine ⟨4813242170938430548715411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12835312455835814796574429 4813242170938430548715411)
      ·
        refine ⟨7219863256407645823073117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4813242170938430548715411 7219863256407645823073117)
        ·
          refine ⟨2707448721152867183652419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7219863256407645823073117 2707448721152867183652419)
          ·
            refine ⟨4061173081729300775478629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707448721152867183652419 4061173081729300775478629)
            ·
              refine ⟨761469952824243895402243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4061173081729300775478629 761469952824243895402243)
              ·
                refine ⟨1142204929236365843103365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761469952824243895402243 1142204929236365843103365)
                ·
                  refine ⟨214163424231818595581881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142204929236365843103365 214163424231818595581881)
                  ·
                    rfl

theorem cell20_469217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_469217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469217 prefixEnd_469217 := by exact prefixLift 469217
  have htrace : WordTrace (prefixWord ++ tailWord_469217) baseStart_469217 baseEnd_469217 := by
    simpa [prefixWord, tailWord_469217, baseEnd_469217] using wordTrace_append hprefix tailTrace_469217
  have hstable : (prefixWord ++ tailWord_469217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469217).length < 2 ^ (prefixWord ++ tailWord_469217).sum := by decide
  have hdescent : baseEnd_469217 < baseStart_469217 := by decide
  rcases family_descends (prefixWord ++ tailWord_469217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469269 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_469269 : Nat := 118140960795 + 469269 * 2 ^ 59
def prefixEnd_469269 : Nat := 4983230072969 + 3 ^ 40 * 469269 * 2
def baseEnd_469269 : Nat := 214187158448737525848335

theorem tailTrace_469269 : CollatzResearch.WordTrace tailWord_469269 prefixEnd_469269 214187158448737525848335 := by
  unfold tailWord_469269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17115646536926032609658861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11410431024617355073105907 17115646536926032609658861)
  ·
    refine ⟨6418367451347262228622073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17115646536926032609658861 6418367451347262228622073)
    ·
      refine ⟨4813775588510446671466555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6418367451347262228622073 4813775588510446671466555)
      ·
        refine ⟨7220663382765670007199833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4813775588510446671466555 7220663382765670007199833)
        ·
          refine ⟨5415497537074252505399875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7220663382765670007199833 5415497537074252505399875)
          ·
            refine ⟨8123246305611378758099813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415497537074252505399875 8123246305611378758099813)
            ·
              refine ⟨1523108682302133517143715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8123246305611378758099813 1523108682302133517143715)
              ·
                refine ⟨2284663023453200275715573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523108682302133517143715 2284663023453200275715573)
                ·
                  refine ⟨214187158448737525848335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2284663023453200275715573 214187158448737525848335)
                  ·
                    rfl

theorem cell20_469269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_469269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469269 prefixEnd_469269 := by exact prefixLift 469269
  have htrace : WordTrace (prefixWord ++ tailWord_469269) baseStart_469269 baseEnd_469269 := by
    simpa [prefixWord, tailWord_469269, baseEnd_469269] using wordTrace_append hprefix tailTrace_469269
  have hstable : (prefixWord ++ tailWord_469269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469269).length < 2 ^ (prefixWord ++ tailWord_469269).sum := by decide
  have hdescent : baseEnd_469269 < baseStart_469269 := by decide
  rcases family_descends (prefixWord ++ tailWord_469269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469282 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_469282 : Nat := 118140960795 + 469282 * 2 ^ 59
def prefixEnd_469282 : Nat := 4983230072969 + 3 ^ 40 * 469282 * 2
def baseEnd_469282 : Nat := 214193092002967258414949

theorem tailTrace_469282 : CollatzResearch.WordTrace tailWord_469282 prefixEnd_469282 214193092002967258414949 := by
  unfold tailWord_469282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4279030171469733957470525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11410747123919290553254733 4279030171469733957470525)
  ·
    refine ⟨1604636314301150234051447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4279030171469733957470525 1604636314301150234051447)
    ·
      refine ⟨2406954471451725351077171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604636314301150234051447 2406954471451725351077171)
      ·
        refine ⟨3610431707177588026615757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406954471451725351077171 3610431707177588026615757)
        ·
          refine ⟨1353911890191595509980909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3610431707177588026615757 1353911890191595509980909)
          ·
            refine ⟨507716958821848316242841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353911890191595509980909 507716958821848316242841)
            ·
              refine ⟨380787719116386237182131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507716958821848316242841 380787719116386237182131)
              ·
                refine ⟨571181578674579355773197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380787719116386237182131 571181578674579355773197)
                ·
                  refine ⟨214193092002967258414949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571181578674579355773197 214193092002967258414949)
                  ·
                    rfl

theorem cell20_469282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_469282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469282 prefixEnd_469282 := by exact prefixLift 469282
  have htrace : WordTrace (prefixWord ++ tailWord_469282) baseStart_469282 baseEnd_469282 := by
    simpa [prefixWord, tailWord_469282, baseEnd_469282] using wordTrace_append hprefix tailTrace_469282
  have hstable : (prefixWord ++ tailWord_469282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469282).length < 2 ^ (prefixWord ++ tailWord_469282).sum := by decide
  have hdescent : baseEnd_469282 < baseStart_469282 := by decide
  rcases family_descends (prefixWord ++ tailWord_469282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469324 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_469324 : Nat := 118140960795 + 469324 * 2 ^ 59
def prefixEnd_469324 : Nat := 4983230072969 + 3 ^ 40 * 469324 * 2
def baseEnd_469324 : Nat := 214212261947401779014777

theorem tailTrace_469324 : CollatzResearch.WordTrace tailWord_469324 prefixEnd_469324 214212261947401779014777 := by
  unfold tailWord_469324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558826275863388501455513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11411768367817851335274017 8558826275863388501455513)
  ·
    refine ⟨6419119706897541376091635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8558826275863388501455513 6419119706897541376091635)
    ·
      refine ⟨9628679560346312064137453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6419119706897541376091635 9628679560346312064137453)
      ·
        refine ⟨3610754835129867024051545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9628679560346312064137453 3610754835129867024051545)
        ·
          refine ⟨2708066126347400268038659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3610754835129867024051545 2708066126347400268038659)
          ·
            refine ⟨4062099189521100402057989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708066126347400268038659 4062099189521100402057989)
            ·
              refine ⟨761643598035206325385873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4062099189521100402057989 761643598035206325385873)
              ·
                refine ⟨571232698526404744039405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761643598035206325385873 571232698526404744039405)
                ·
                  refine ⟨214212261947401779014777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571232698526404744039405 214212261947401779014777)
                  ·
                    rfl

theorem cell20_469324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_469324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469324 prefixEnd_469324 := by exact prefixLift 469324
  have htrace : WordTrace (prefixWord ++ tailWord_469324) baseStart_469324 baseEnd_469324 := by
    simpa [prefixWord, tailWord_469324, baseEnd_469324] using wordTrace_append hprefix tailTrace_469324
  have hstable : (prefixWord ++ tailWord_469324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469324).length < 2 ^ (prefixWord ++ tailWord_469324).sum := by decide
  have hdescent : baseEnd_469324 < baseStart_469324 := by decide
  rcases family_descends (prefixWord ++ tailWord_469324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469365 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 2]
def baseStart_469365 : Nat := 118140960795 + 469365 * 2 ^ 59
def prefixEnd_469365 : Nat := 4983230072969 + 3 ^ 40 * 469365 * 2
def baseEnd_469365 : Nat := 214230975464587858647943

theorem tailTrace_469365 : CollatzResearch.WordTrace tailWord_469365 prefixEnd_469365 214230975464587858647943 := by
  unfold tailWord_469365
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119147944578241005153549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11412765296385494003435699 17119147944578241005153549)
  ·
    refine ⟨6419680479216840376932581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17119147944578241005153549 6419680479216840376932581)
    ·
      refine ⟨1203690089853157570674859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6419680479216840376932581 1203690089853157570674859)
      ·
        refine ⟨1805535134779736356012289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203690089853157570674859 1805535134779736356012289)
        ·
          refine ⟨1354151351084802267009217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805535134779736356012289 1354151351084802267009217)
          ·
            refine ⟨1015613513313601700256913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354151351084802267009217 1015613513313601700256913)
            ·
              refine ⟨761710134985201275192685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015613513313601700256913 761710134985201275192685)
              ·
                refine ⟨285641300619450478197257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 761710134985201275192685 285641300619450478197257)
                ·
                  refine ⟨214230975464587858647943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285641300619450478197257 214230975464587858647943)
                  ·
                    rfl

theorem cell20_469365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_469365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469365 prefixEnd_469365 := by exact prefixLift 469365
  have htrace : WordTrace (prefixWord ++ tailWord_469365) baseStart_469365 baseEnd_469365 := by
    simpa [prefixWord, tailWord_469365, baseEnd_469365] using wordTrace_append hprefix tailTrace_469365
  have hstable : (prefixWord ++ tailWord_469365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469365).length < 2 ^ (prefixWord ++ tailWord_469365).sum := by decide
  have hdescent : baseEnd_469365 < baseStart_469365 := by decide
  rcases family_descends (prefixWord ++ tailWord_469365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469379 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 3]
def baseStart_469379 : Nat := 118140960795 + 469379 * 2 ^ 59
def prefixEnd_469379 : Nat := 4983230072969 + 3 ^ 40 * 469379 * 2
def baseEnd_469379 : Nat := 214237365446066032181219

theorem tailTrace_469379 : CollatzResearch.WordTrace tailWord_469379 prefixEnd_469379 214237365446066032181219 := by
  unfold tailWord_469379
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119658566527521396163191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11413105711018347597442127 17119658566527521396163191)
  ·
    refine ⟨25679487849791282094244787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17119658566527521396163191 25679487849791282094244787)
    ·
      refine ⟨38519231774686923141367181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25679487849791282094244787 38519231774686923141367181)
      ·
        refine ⟨14444711915507596178012693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38519231774686923141367181 14444711915507596178012693)
        ·
          refine ⟨677095871039418570844345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14444711915507596178012693 677095871039418570844345)
          ·
            refine ⟨507821903279563928133259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677095871039418570844345 507821903279563928133259)
            ·
              refine ⟨761732854919345892199889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507821903279563928133259 761732854919345892199889)
              ·
                refine ⟨571299641189509419149917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761732854919345892199889 571299641189509419149917)
                ·
                  refine ⟨214237365446066032181219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571299641189509419149917 214237365446066032181219)
                  ·
                    rfl

theorem cell20_469379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_469379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469379 prefixEnd_469379 := by exact prefixLift 469379
  have htrace : WordTrace (prefixWord ++ tailWord_469379) baseStart_469379 baseEnd_469379 := by
    simpa [prefixWord, tailWord_469379, baseEnd_469379] using wordTrace_append hprefix tailTrace_469379
  have hstable : (prefixWord ++ tailWord_469379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469379).length < 2 ^ (prefixWord ++ tailWord_469379).sum := by decide
  have hdescent : baseEnd_469379 < baseStart_469379 := by decide
  rcases family_descends (prefixWord ++ tailWord_469379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469383 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_469383 : Nat := 118140960795 + 469383 * 2 ^ 59
def prefixEnd_469383 : Nat := 4983230072969 + 3 ^ 40 * 469383 * 2
def baseEnd_469383 : Nat := 214239191155059796047869

theorem tailTrace_469383 : CollatzResearch.WordTrace tailWord_469383 prefixEnd_469383 214239191155059796047869 := by
  unfold tailWord_469383
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119804458513030079308803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11413202972342020052872535 17119804458513030079308803)
  ·
    refine ⟨25679706687769545118963205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17119804458513030079308803 25679706687769545118963205)
    ·
      refine ⟨4814945003956789709805601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25679706687769545118963205 4814945003956789709805601)
      ·
        refine ⟨3611208752967592282354201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4814945003956789709805601 3611208752967592282354201)
        ·
          refine ⟨2708406564725694211765651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3611208752967592282354201 2708406564725694211765651)
          ·
            refine ⟨4062609847088541317648477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708406564725694211765651 4062609847088541317648477)
            ·
              refine ⟨1523478692658202994118179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4062609847088541317648477 1523478692658202994118179)
              ·
                refine ⟨2285218038987304491177269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523478692658202994118179 2285218038987304491177269)
                ·
                  refine ⟨214239191155059796047869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2285218038987304491177269 214239191155059796047869)
                  ·
                    rfl

theorem cell20_469383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_469383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469383 prefixEnd_469383 := by exact prefixLift 469383
  have htrace : WordTrace (prefixWord ++ tailWord_469383) baseStart_469383 baseEnd_469383 := by
    simpa [prefixWord, tailWord_469383, baseEnd_469383] using wordTrace_append hprefix tailTrace_469383
  have hstable : (prefixWord ++ tailWord_469383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469383).length < 2 ^ (prefixWord ++ tailWord_469383).sum := by decide
  have hdescent : baseEnd_469383 < baseStart_469383 := by decide
  rcases family_descends (prefixWord ++ tailWord_469383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469396 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_469396 : Nat := 118140960795 + 469396 * 2 ^ 59
def prefixEnd_469396 : Nat := 4983230072969 + 3 ^ 40 * 469396 * 2
def baseEnd_469396 : Nat := 214245124709289528614483

theorem tailTrace_469396 : CollatzResearch.WordTrace tailWord_469396 prefixEnd_469396 214245124709289528614483 := by
  unfold tailWord_469396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560139303732966649766021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11413519071643955533021361 8560139303732966649766021)
  ·
    refine ⟨1605026119449931246831129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8560139303732966649766021 1605026119449931246831129)
    ·
      refine ⟨1203769589587448435123347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1605026119449931246831129 1203769589587448435123347)
      ·
        refine ⟨1805654384381172652685021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203769589587448435123347 1805654384381172652685021)
        ·
          refine ⟨677120394142939744756883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1805654384381172652685021 677120394142939744756883)
          ·
            refine ⟨1015680591214409617135325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677120394142939744756883 1015680591214409617135325)
            ·
              refine ⟨380880221705403606425747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015680591214409617135325 380880221705403606425747)
              ·
                refine ⟨571320332558105409638621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380880221705403606425747 571320332558105409638621)
                ·
                  refine ⟨214245124709289528614483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571320332558105409638621 214245124709289528614483)
                  ·
                    rfl

theorem cell20_469396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_469396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469396 prefixEnd_469396 := by exact prefixLift 469396
  have htrace : WordTrace (prefixWord ++ tailWord_469396) baseStart_469396 baseEnd_469396 := by
    simpa [prefixWord, tailWord_469396, baseEnd_469396] using wordTrace_append hprefix tailTrace_469396
  have hstable : (prefixWord ++ tailWord_469396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469396).length < 2 ^ (prefixWord ++ tailWord_469396).sum := by decide
  have hdescent : baseEnd_469396 < baseStart_469396 := by decide
  rcases family_descends (prefixWord ++ tailWord_469396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469397 : List Nat := [1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_469397 : Nat := 118140960795 + 469397 * 2 ^ 59
def prefixEnd_469397 : Nat := 4983230072969 + 3 ^ 40 * 469397 * 2
def baseEnd_469397 : Nat := 71415193712179323193715

theorem tailTrace_469397 : CollatzResearch.WordTrace tailWord_469397 prefixEnd_469397 71415193712179323193715 := by
  unfold tailWord_469397
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120315080462310470318445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11413543386974873646878963 17120315080462310470318445)
  ·
    refine ⟨6420118155173366426369417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17120315080462310470318445 6420118155173366426369417)
    ·
      refine ⟨4815088616380024819777063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6420118155173366426369417 4815088616380024819777063)
      ·
        refine ⟨7222632924570037229665595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815088616380024819777063 7222632924570037229665595)
        ·
          refine ⟨10833949386855055844498393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222632924570037229665595 10833949386855055844498393)
          ·
            refine ⟨8125462040141291883373795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10833949386855055844498393 8125462040141291883373795)
            ·
              refine ⟨12188193060211937825060693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125462040141291883373795 12188193060211937825060693)
              ·
                refine ⟨71415193712179323193715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12188193060211937825060693 71415193712179323193715)
                ·
                  rfl

theorem cell20_469397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_469397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469397 prefixEnd_469397 := by exact prefixLift 469397
  have htrace : WordTrace (prefixWord ++ tailWord_469397) baseStart_469397 baseEnd_469397 := by
    simpa [prefixWord, tailWord_469397, baseEnd_469397] using wordTrace_append hprefix tailTrace_469397
  have hstable : (prefixWord ++ tailWord_469397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469397).length < 2 ^ (prefixWord ++ tailWord_469397).sum := by decide
  have hdescent : baseEnd_469397 < baseStart_469397 := by decide
  rcases family_descends (prefixWord ++ tailWord_469397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469466 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_469466 : Nat := 118140960795 + 469466 * 2 ^ 59
def prefixEnd_469466 : Nat := 4983230072969 + 3 ^ 40 * 469466 * 2
def baseEnd_469466 : Nat := 214277074616680396280863

theorem tailTrace_469466 : CollatzResearch.WordTrace tailWord_469466 prefixEnd_469466 214277074616680396280863 := by
  unfold tailWord_469466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280707929303083813645063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11415221144808223503053501 4280707929303083813645063)
  ·
    refine ⟨6421061893954625720467595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4280707929303083813645063 6421061893954625720467595)
    ·
      refine ⟨9631592840931938580701393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421061893954625720467595 9631592840931938580701393)
      ·
        refine ⟨7223694630698953935526045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9631592840931938580701393 7223694630698953935526045)
        ·
          refine ⟨2708885486512107725822267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7223694630698953935526045 2708885486512107725822267)
          ·
            refine ⟨4063328229768161588733401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708885486512107725822267 4063328229768161588733401)
            ·
              refine ⟨3047496172326121191550051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063328229768161588733401 3047496172326121191550051)
              ·
                refine ⟨4571244258489181787325077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047496172326121191550051 4571244258489181787325077)
                ·
                  refine ⟨214277074616680396280863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4571244258489181787325077 214277074616680396280863)
                  ·
                    rfl

theorem cell20_469466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_469466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469466 prefixEnd_469466 := by exact prefixLift 469466
  have htrace : WordTrace (prefixWord ++ tailWord_469466) baseStart_469466 baseEnd_469466 := by
    simpa [prefixWord, tailWord_469466, baseEnd_469466] using wordTrace_append hprefix tailTrace_469466
  have hstable : (prefixWord ++ tailWord_469466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469466).length < 2 ^ (prefixWord ++ tailWord_469466).sum := by decide
  have hdescent : baseEnd_469466 < baseStart_469466 := by decide
  rcases family_descends (prefixWord ++ tailWord_469466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469473 : List Nat := [1, 2, 3, 1, 2, 2, 1, 8]
def baseStart_469473 : Nat := 118140960795 + 469473 * 2 ^ 59
def prefixEnd_469473 : Nat := 4983230072969 + 3 ^ 40 * 469473 * 2
def baseEnd_469473 : Nat := 71426756535806494349167

theorem tailTrace_469473 : CollatzResearch.WordTrace tailWord_469473 prefixEnd_469473 71426756535806494349167 := by
  unfold tailWord_469473
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123087028186975450085073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11415391352124650300056715 17123087028186975450085073)
  ·
    refine ⟨12842315271140231587563805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17123087028186975450085073 12842315271140231587563805)
    ·
      refine ⟨4815868226677586845336427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12842315271140231587563805 4815868226677586845336427)
      ·
        refine ⟨7223802340016380268004641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815868226677586845336427 7223802340016380268004641)
        ·
          refine ⟨5417851755012285201003481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7223802340016380268004641 5417851755012285201003481)
          ·
            refine ⟨4063388816259213900752611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5417851755012285201003481 4063388816259213900752611)
            ·
              refine ⟨6095083224388820851128917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063388816259213900752611 6095083224388820851128917)
              ·
                refine ⟨71426756535806494349167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6095083224388820851128917 71426756535806494349167)
                ·
                  rfl

theorem cell20_469473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_469473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469473 prefixEnd_469473 := by exact prefixLift 469473
  have htrace : WordTrace (prefixWord ++ tailWord_469473) baseStart_469473 baseEnd_469473 := by
    simpa [prefixWord, tailWord_469473, baseEnd_469473] using wordTrace_append hprefix tailTrace_469473
  have hstable : (prefixWord ++ tailWord_469473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469473).length < 2 ^ (prefixWord ++ tailWord_469473).sum := by decide
  have hdescent : baseEnd_469473 < baseStart_469473 := by decide
  rcases family_descends (prefixWord ++ tailWord_469473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469483 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 2]
def baseStart_469483 : Nat := 118140960795 + 469483 * 2 ^ 59
def prefixEnd_469483 : Nat := 4983230072969 + 3 ^ 40 * 469483 * 2
def baseEnd_469483 : Nat := 214284833879903892714127

theorem tailTrace_469483 : CollatzResearch.WordTrace tailWord_469483 prefixEnd_469483 214284833879903892714127 := by
  unfold tailWord_469483
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123451758150747157949103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11415634505433831438632735 17123451758150747157949103)
  ·
    refine ⟨25685177637226120736923655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17123451758150747157949103 25685177637226120736923655)
    ·
      refine ⟨38527766455839181105385483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25685177637226120736923655 38527766455839181105385483)
      ·
        refine ⟨57791649683758771658078225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38527766455839181105385483 57791649683758771658078225)
        ·
          refine ⟨43343737262819078743558669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57791649683758771658078225 43343737262819078743558669)
          ·
            refine ⟨16253901473557154528834501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43343737262819078743558669 16253901473557154528834501)
            ·
              refine ⟨3047606526291966474156469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16253901473557154528834501 3047606526291966474156469)
              ·
                refine ⟨285713111839871856952169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3047606526291966474156469 285713111839871856952169)
                ·
                  refine ⟨214284833879903892714127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285713111839871856952169 214284833879903892714127)
                  ·
                    rfl

theorem cell20_469483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 2].length) (baseStart_469483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469483 prefixEnd_469483 := by exact prefixLift 469483
  have htrace : WordTrace (prefixWord ++ tailWord_469483) baseStart_469483 baseEnd_469483 := by
    simpa [prefixWord, tailWord_469483, baseEnd_469483] using wordTrace_append hprefix tailTrace_469483
  have hstable : (prefixWord ++ tailWord_469483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469483).length < 2 ^ (prefixWord ++ tailWord_469483).sum := by decide
  have hdescent : baseEnd_469483 < baseStart_469483 := by decide
  rcases family_descends (prefixWord ++ tailWord_469483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469490 : List Nat := [3, 2, 1, 4, 2, 8]
def baseStart_469490 : Nat := 118140960795 + 469490 * 2 ^ 59
def prefixEnd_469490 : Nat := 4983230072969 + 3 ^ 40 * 469490 * 2
def baseEnd_469490 : Nat := 7936593661875665906695

theorem tailTrace_469490 : CollatzResearch.WordTrace tailWord_469490 prefixEnd_469490 7936593661875665906695 := by
  unfold tailWord_469490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280926767281346838363481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11415804712750258235635949 4280926767281346838363481)
  ·
    refine ⟨3210695075461010128772611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4280926767281346838363481 3210695075461010128772611)
    ·
      refine ⟨4816042613191515193158917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210695075461010128772611 4816042613191515193158917)
      ·
        refine ⟨903007989973409098717297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4816042613191515193158917 903007989973409098717297)
        ·
          refine ⟨677255992480056824037973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903007989973409098717297 677255992480056824037973)
          ·
            refine ⟨7936593661875665906695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 677255992480056824037973 7936593661875665906695)
            ·
              rfl

theorem cell20_469490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 8].length) (baseStart_469490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469490 prefixEnd_469490 := by exact prefixLift 469490
  have htrace : WordTrace (prefixWord ++ tailWord_469490) baseStart_469490 baseEnd_469490 := by
    simpa [prefixWord, tailWord_469490, baseEnd_469490] using wordTrace_append hprefix tailTrace_469490
  have hstable : (prefixWord ++ tailWord_469490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469490).length < 2 ^ (prefixWord ++ tailWord_469490).sum := by decide
  have hdescent : baseEnd_469490 < baseStart_469490 := by decide
  rcases family_descends (prefixWord ++ tailWord_469490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469497 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_469497 : Nat := 118140960795 + 469497 * 2 ^ 59
def prefixEnd_469497 : Nat := 4983230072969 + 3 ^ 40 * 469497 * 2
def baseEnd_469497 : Nat := 214291223861382066247403

theorem tailTrace_469497 : CollatzResearch.WordTrace tailWord_469497 prefixEnd_469497 214291223861382066247403 := by
  unfold tailWord_469497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123962380100027548958745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11415974920066685032639163 17123962380100027548958745)
  ·
    refine ⟨12842971785075020661719059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17123962380100027548958745 12842971785075020661719059)
    ·
      refine ⟨19264457677612530992578589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12842971785075020661719059 19264457677612530992578589)
      ·
        refine ⟨7224171629104699122216971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19264457677612530992578589 7224171629104699122216971)
        ·
          refine ⟨10836257443657048683325457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224171629104699122216971 10836257443657048683325457)
          ·
            refine ⟨8127193082742786512494093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10836257443657048683325457 8127193082742786512494093)
            ·
              refine ⟨3047697406028544942185285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8127193082742786512494093 3047697406028544942185285)
              ·
                refine ⟨571443263630352176659741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3047697406028544942185285 571443263630352176659741)
                ·
                  refine ⟨214291223861382066247403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571443263630352176659741 214291223861382066247403)
                  ·
                    rfl

theorem cell20_469497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_469497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469497 prefixEnd_469497 := by exact prefixLift 469497
  have htrace : WordTrace (prefixWord ++ tailWord_469497) baseStart_469497 baseEnd_469497 := by
    simpa [prefixWord, tailWord_469497, baseEnd_469497] using wordTrace_append hprefix tailTrace_469497
  have hstable : (prefixWord ++ tailWord_469497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469497).length < 2 ^ (prefixWord ++ tailWord_469497).sum := by decide
  have hdescent : baseEnd_469497 < baseStart_469497 := by decide
  rcases family_descends (prefixWord ++ tailWord_469497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469517 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 4]
def baseStart_469517 : Nat := 118140960795 + 469517 * 2 ^ 59
def prefixEnd_469517 : Nat := 4983230072969 + 3 ^ 40 * 469517 * 2
def baseEnd_469517 : Nat := 214300352406350885580655

theorem tailTrace_469517 : CollatzResearch.WordTrace tailWord_469517 prefixEnd_469517 214300352406350885580655 := by
  unfold tailWord_469517
  simp only [CollatzResearch.WordTrace]
  refine ⟨17124691840027570964686805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11416461226685047309791203 17124691840027570964686805)
  ·
    refine ⟨401359965000646194484847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17124691840027570964686805 401359965000646194484847)
    ·
      refine ⟨602039947500969291727271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401359965000646194484847 602039947500969291727271)
      ·
        refine ⟨903059921251453937590907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602039947500969291727271 903059921251453937590907)
        ·
          refine ⟨1354589881877180906386361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903059921251453937590907 1354589881877180906386361)
          ·
            refine ⟨1015942411407885679789771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354589881877180906386361 1015942411407885679789771)
            ·
              refine ⟨1523913617111828519684657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015942411407885679789771 1523913617111828519684657)
              ·
                refine ⟨1142935212833871389763493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523913617111828519684657 1142935212833871389763493)
                ·
                  refine ⟨214300352406350885580655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142935212833871389763493 214300352406350885580655)
                  ·
                    rfl

theorem cell20_469517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_469517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469517 prefixEnd_469517 := by exact prefixLift 469517
  have htrace : WordTrace (prefixWord ++ tailWord_469517) baseStart_469517 baseEnd_469517 := by
    simpa [prefixWord, tailWord_469517, baseEnd_469517] using wordTrace_append hprefix tailTrace_469517
  have hstable : (prefixWord ++ tailWord_469517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469517).length < 2 ^ (prefixWord ++ tailWord_469517).sum := by decide
  have hdescent : baseEnd_469517 < baseStart_469517 := by decide
  rcases family_descends (prefixWord ++ tailWord_469517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469524 : List Nat := [2, 4, 3, 1, 1, 2, 3, 4]
def baseStart_469524 : Nat := 118140960795 + 469524 * 2 ^ 59
def prefixEnd_469524 : Nat := 4983230072969 + 3 ^ 40 * 469524 * 2
def baseEnd_469524 : Nat := 71434515799029990782431

theorem tailTrace_469524 : CollatzResearch.WordTrace tailWord_469524 prefixEnd_469524 71434515799029990782431 := by
  unfold tailWord_469524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562473575501105580095813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11416631434001474106794417 8562473575501105580095813)
  ·
    refine ⟨1605463795406457296267965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8562473575501105580095813 1605463795406457296267965)
    ·
      refine ⟨602048923277421486100487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1605463795406457296267965 602048923277421486100487)
      ·
        refine ⟨903073384916132229150731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602048923277421486100487 903073384916132229150731)
        ·
          refine ⟨1354610077374198343726097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903073384916132229150731 1354610077374198343726097)
          ·
            refine ⟨1015957558030648757794573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354610077374198343726097 1015957558030648757794573)
            ·
              refine ⟨380984084261493284172965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015957558030648757794573 380984084261493284172965)
              ·
                refine ⟨71434515799029990782431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380984084261493284172965 71434515799029990782431)
                ·
                  rfl

theorem cell20_469524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_469524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469524 prefixEnd_469524 := by exact prefixLift 469524
  have htrace : WordTrace (prefixWord ++ tailWord_469524) baseStart_469524 baseEnd_469524 := by
    simpa [prefixWord, tailWord_469524, baseEnd_469524] using wordTrace_append hprefix tailTrace_469524
  have hstable : (prefixWord ++ tailWord_469524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469524).length < 2 ^ (prefixWord ++ tailWord_469524).sum := by decide
  have hdescent : baseEnd_469524 < baseStart_469524 := by decide
  rcases family_descends (prefixWord ++ tailWord_469524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469559 : List Nat := [1, 1, 3, 1, 2, 3, 1, 6, 2]
def baseStart_469559 : Nat := 118140960795 + 469559 * 2 ^ 59
def prefixEnd_469559 : Nat := 4983230072969 + 3 ^ 40 * 469559 * 2
def baseEnd_469559 : Nat := 214319522350785406180483

theorem tailTrace_469559 : CollatzResearch.WordTrace tailWord_469559 prefixEnd_469559 214319522350785406180483 := by
  unfold tailWord_469559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17126223705875412137715731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11417482470583608091810487 17126223705875412137715731)
  ·
    refine ⟨25689335558813118206573597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17126223705875412137715731 25689335558813118206573597)
    ·
      refine ⟨9633500834554919327465099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25689335558813118206573597 9633500834554919327465099)
      ·
        refine ⟨14450251251832378991197649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9633500834554919327465099 14450251251832378991197649)
        ·
          refine ⟨10837688438874284243398237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14450251251832378991197649 10837688438874284243398237)
          ·
            refine ⟨4064133164577856591274339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10837688438874284243398237 4064133164577856591274339)
            ·
              refine ⟨6096199746866784886911509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064133164577856591274339 6096199746866784886911509)
              ·
                refine ⟨285759363134380541573977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6096199746866784886911509 285759363134380541573977)
                ·
                  refine ⟨214319522350785406180483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285759363134380541573977 214319522350785406180483)
                  ·
                    rfl

theorem cell20_469559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 2].length) (baseStart_469559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469559 prefixEnd_469559 := by exact prefixLift 469559
  have htrace : WordTrace (prefixWord ++ tailWord_469559) baseStart_469559 baseEnd_469559 := by
    simpa [prefixWord, tailWord_469559, baseEnd_469559] using wordTrace_append hprefix tailTrace_469559
  have hstable : (prefixWord ++ tailWord_469559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469559).length < 2 ^ (prefixWord ++ tailWord_469559).sum := by decide
  have hdescent : baseEnd_469559 < baseStart_469559 := by decide
  rcases family_descends (prefixWord ++ tailWord_469559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469569 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 3]
def baseStart_469569 : Nat := 118140960795 + 469569 * 2 ^ 59
def prefixEnd_469569 : Nat := 4983230072969 + 3 ^ 40 * 469569 * 2
def baseEnd_469569 : Nat := 214324086623269815847109

theorem tailTrace_469569 : CollatzResearch.WordTrace tailWord_469569 prefixEnd_469569 214324086623269815847109 := by
  unfold tailWord_469569
  simp only [CollatzResearch.WordTrace]
  refine ⟨17126588435839183845579761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11417725623892789230386507 17126588435839183845579761)
  ·
    refine ⟨12844941326879387884184821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17126588435839183845579761 12844941326879387884184821)
    ·
      refine ⟨1204213249394942614142327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12844941326879387884184821 1204213249394942614142327)
      ·
        refine ⟨1806319874092413921213491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204213249394942614142327 1806319874092413921213491)
        ·
          refine ⟨2709479811138620881820237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806319874092413921213491 2709479811138620881820237)
          ·
            refine ⟨1016054929176982830682589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2709479811138620881820237 1016054929176982830682589)
            ·
              refine ⟨381020598441368561505971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016054929176982830682589 381020598441368561505971)
              ·
                refine ⟨571530897662052842258957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381020598441368561505971 571530897662052842258957)
                ·
                  refine ⟨214324086623269815847109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571530897662052842258957 214324086623269815847109)
                  ·
                    rfl

theorem cell20_469569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_469569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469569 prefixEnd_469569 := by exact prefixLift 469569
  have htrace : WordTrace (prefixWord ++ tailWord_469569) baseStart_469569 baseEnd_469569 := by
    simpa [prefixWord, tailWord_469569, baseEnd_469569] using wordTrace_append hprefix tailTrace_469569
  have hstable : (prefixWord ++ tailWord_469569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469569).length < 2 ^ (prefixWord ++ tailWord_469569).sum := by decide
  have hdescent : baseEnd_469569 < baseStart_469569 := by decide
  rcases family_descends (prefixWord ++ tailWord_469569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469580 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_469580 : Nat := 118140960795 + 469580 * 2 ^ 59
def prefixEnd_469580 : Nat := 4983230072969 + 3 ^ 40 * 469580 * 2
def baseEnd_469580 : Nat := 214329107323002666480397

theorem tailTrace_469580 : CollatzResearch.WordTrace tailWord_469580 prefixEnd_469580 214329107323002666480397 := by
  unfold tailWord_469580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563494819399666362115097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11417993092532888482820129 8563494819399666362115097)
  ·
    refine ⟨6422621114549749771586323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8563494819399666362115097 6422621114549749771586323)
    ·
      refine ⟨9633931671824624657379485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6422621114549749771586323 9633931671824624657379485)
      ·
        refine ⟨3612724376934234246517307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9633931671824624657379485 3612724376934234246517307)
        ·
          refine ⟨5419086565401351369775961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612724376934234246517307 5419086565401351369775961)
          ·
            refine ⟨4064314924051013527331971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419086565401351369775961 4064314924051013527331971)
            ·
              refine ⟨6096472386076520290997957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064314924051013527331971 6096472386076520290997957)
              ·
                refine ⟨1143088572389347554562117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6096472386076520290997957 1143088572389347554562117)
                ·
                  refine ⟨214329107323002666480397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143088572389347554562117 214329107323002666480397)
                  ·
                    rfl

theorem cell20_469580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_469580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469580 prefixEnd_469580 := by exact prefixLift 469580
  have htrace : WordTrace (prefixWord ++ tailWord_469580) baseStart_469580 baseEnd_469580 := by
    simpa [prefixWord, tailWord_469580, baseEnd_469580] using wordTrace_append hprefix tailTrace_469580
  have hstable : (prefixWord ++ tailWord_469580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469580).length < 2 ^ (prefixWord ++ tailWord_469580).sum := by decide
  have hdescent : baseEnd_469580 < baseStart_469580 := by decide
  rcases family_descends (prefixWord ++ tailWord_469580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469614 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_469614 : Nat := 118140960795 + 469614 * 2 ^ 59
def prefixEnd_469614 : Nat := 4983230072969 + 3 ^ 40 * 469614 * 2
def baseEnd_469614 : Nat := 214344625849449659346925

theorem tailTrace_469614 : CollatzResearch.WordTrace tailWord_469614 prefixEnd_469614 214344625849449659346925 := by
  unfold tailWord_469614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141028715084519566370987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11418819813784104353978597 2141028715084519566370987)
  ·
    refine ⟨3211543072626779349556481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2141028715084519566370987 3211543072626779349556481)
    ·
      refine ⟨2408657304470084512167361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3211543072626779349556481 2408657304470084512167361)
      ·
        refine ⟨1806492978352563384125521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408657304470084512167361 1806492978352563384125521)
        ·
          refine ⟨1354869733764422538094141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806492978352563384125521 1354869733764422538094141)
          ·
            refine ⟨508076150161658451785303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1354869733764422538094141 508076150161658451785303)
            ·
              refine ⟨762114225242487677677955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508076150161658451785303 762114225242487677677955)
              ·
                refine ⟨1143171337863731516516933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762114225242487677677955 1143171337863731516516933)
                ·
                  refine ⟨214344625849449659346925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143171337863731516516933 214344625849449659346925)
                  ·
                    rfl

theorem cell20_469614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_469614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469614 prefixEnd_469614 := by exact prefixLift 469614
  have htrace : WordTrace (prefixWord ++ tailWord_469614) baseStart_469614 baseEnd_469614 := by
    simpa [prefixWord, tailWord_469614, baseEnd_469614] using wordTrace_append hprefix tailTrace_469614
  have hstable : (prefixWord ++ tailWord_469614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469614).length < 2 ^ (prefixWord ++ tailWord_469614).sum := by decide
  have hdescent : baseEnd_469614 < baseStart_469614 := by decide
  rcases family_descends (prefixWord ++ tailWord_469614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469621 : List Nat := [1, 3, 4, 2, 2, 1, 2, 5]
def baseStart_469621 : Nat := 118140960795 + 469621 * 2 ^ 59
def prefixEnd_469621 : Nat := 4983230072969 + 3 ^ 40 * 469621 * 2
def baseEnd_469621 : Nat := 71449273613396248704521

theorem tailTrace_469621 : CollatzResearch.WordTrace tailWord_469621 prefixEnd_469621 71449273613396248704521 := by
  unfold tailWord_469621
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128485031650796726472717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11418990021100531150981811 17128485031650796726472717)
  ·
    refine ⟨6423181886869048772427269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17128485031650796726472717 6423181886869048772427269)
    ·
      refine ⟨1204346603787946644830113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6423181886869048772427269 1204346603787946644830113)
      ·
        refine ⟨903259952840959983622585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204346603787946644830113 903259952840959983622585)
        ·
          refine ⟨677444964630719987716939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903259952840959983622585 677444964630719987716939)
          ·
            refine ⟨1016167446946079981575409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677444964630719987716939 1016167446946079981575409)
            ·
              refine ⟨762125585209559986181557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016167446946079981575409 762125585209559986181557)
              ·
                refine ⟨71449273613396248704521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762125585209559986181557 71449273613396248704521)
                ·
                  rfl

theorem cell20_469621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_469621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469621 prefixEnd_469621 := by exact prefixLift 469621
  have htrace : WordTrace (prefixWord ++ tailWord_469621) baseStart_469621 baseEnd_469621 := by
    simpa [prefixWord, tailWord_469621, baseEnd_469621] using wordTrace_append hprefix tailTrace_469621
  have hstable : (prefixWord ++ tailWord_469621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469621).length < 2 ^ (prefixWord ++ tailWord_469621).sum := by decide
  have hdescent : baseEnd_469621 < baseStart_469621 := by decide
  rcases family_descends (prefixWord ++ tailWord_469621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469625 : List Nat := [1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_469625 : Nat := 118140960795 + 469625 * 2 ^ 59
def prefixEnd_469625 : Nat := 4983230072969 + 3 ^ 40 * 469625 * 2
def baseEnd_469625 : Nat := 71449882183060836660071

theorem tailTrace_469625 : CollatzResearch.WordTrace tailWord_469625 prefixEnd_469625 71449882183060836660071 := by
  unfold tailWord_469625
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128630923636305409618329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11419087282424203606412219 17128630923636305409618329)
  ·
    refine ⟨12846473192727229057213747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17128630923636305409618329 12846473192727229057213747)
    ·
      refine ⟨19269709789090843585820621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12846473192727229057213747 19269709789090843585820621)
      ·
        refine ⟨7226141170909066344682733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19269709789090843585820621 7226141170909066344682733)
        ·
          refine ⟨2709802939090899879256025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7226141170909066344682733 2709802939090899879256025)
          ·
            refine ⟨2032352204318174909442019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2709802939090899879256025 2032352204318174909442019)
            ·
              refine ⟨3048528306477262364163029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032352204318174909442019 3048528306477262364163029)
              ·
                refine ⟨71449882183060836660071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3048528306477262364163029 71449882183060836660071)
                ·
                  rfl

theorem cell20_469625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_469625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469625 prefixEnd_469625 := by exact prefixLift 469625
  have htrace : WordTrace (prefixWord ++ tailWord_469625) baseStart_469625 baseEnd_469625 := by
    simpa [prefixWord, tailWord_469625, baseEnd_469625] using wordTrace_append hprefix tailTrace_469625
  have hstable : (prefixWord ++ tailWord_469625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469625).length < 2 ^ (prefixWord ++ tailWord_469625).sum := by decide
  have hdescent : baseEnd_469625 < baseStart_469625 := by decide
  rcases family_descends (prefixWord ++ tailWord_469625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469628 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_469628 : Nat := 118140960795 + 469628 * 2 ^ 59
def prefixEnd_469628 : Nat := 4983230072969 + 3 ^ 40 * 469628 * 2
def baseEnd_469628 : Nat := 214351015830927832880201

theorem tailTrace_469628 : CollatzResearch.WordTrace tailWord_469628 prefixEnd_469628 214351015830927832880201 := by
  unfold tailWord_469628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8564370171312718460988769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11419160228416957947985025 8564370171312718460988769)
  ·
    refine ⟨6423277628484538845741577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8564370171312718460988769 6423277628484538845741577)
    ·
      refine ⟨4817458221363404134306183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6423277628484538845741577 4817458221363404134306183)
      ·
        refine ⟨7226187332045106201459275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4817458221363404134306183 7226187332045106201459275)
        ·
          refine ⟨10839280998067659302188913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226187332045106201459275 10839280998067659302188913)
          ·
            refine ⟨8129460748550744476641685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10839280998067659302188913 8129460748550744476641685)
            ·
              refine ⟨381068472588316147342579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8129460748550744476641685 381068472588316147342579)
              ·
                refine ⟨571602708882474221013869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381068472588316147342579 571602708882474221013869)
                ·
                  refine ⟨214351015830927832880201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571602708882474221013869 214351015830927832880201)
                  ·
                    rfl

theorem cell20_469628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_469628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469628 prefixEnd_469628 := by exact prefixLift 469628
  have htrace : WordTrace (prefixWord ++ tailWord_469628) baseStart_469628 baseEnd_469628 := by
    simpa [prefixWord, tailWord_469628, baseEnd_469628] using wordTrace_append hprefix tailTrace_469628
  have hstable : (prefixWord ++ tailWord_469628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469628).length < 2 ^ (prefixWord ++ tailWord_469628).sum := by decide
  have hdescent : baseEnd_469628 < baseStart_469628 := by decide
  rcases family_descends (prefixWord ++ tailWord_469628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469732 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_469732 : Nat := 118140960795 + 469732 * 2 ^ 59
def prefixEnd_469732 : Nat := 4983230072969 + 3 ^ 40 * 469732 * 2
def baseEnd_469732 : Nat := 214398484264765693413109

theorem tailTrace_469732 : CollatzResearch.WordTrace tailWord_469732 prefixEnd_469732 214398484264765693413109 := by
  unfold tailWord_469732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566266767124331341881725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11421689022832441789175633 8566266767124331341881725)
  ·
    refine ⟨3212350037671624253205647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8566266767124331341881725 3212350037671624253205647)
    ·
      refine ⟨4818525056507436379808471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3212350037671624253205647 4818525056507436379808471)
      ·
        refine ⟨7227787584761154569712707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4818525056507436379808471 7227787584761154569712707)
        ·
          refine ⟨10841681377141731854569061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7227787584761154569712707 10841681377141731854569061)
          ·
            refine ⟨2032815258214074722731699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10841681377141731854569061 2032815258214074722731699)
            ·
              refine ⟨3049222887321112084097549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032815258214074722731699 3049222887321112084097549)
              ·
                refine ⟨1143458582745417031536581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049222887321112084097549 1143458582745417031536581)
                ·
                  refine ⟨214398484264765693413109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1143458582745417031536581 214398484264765693413109)
                  ·
                    rfl

theorem cell20_469732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_469732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469732 prefixEnd_469732 := by exact prefixLift 469732
  have htrace : WordTrace (prefixWord ++ tailWord_469732) baseStart_469732 baseEnd_469732 := by
    simpa [prefixWord, tailWord_469732, baseEnd_469732] using wordTrace_append hprefix tailTrace_469732
  have hstable : (prefixWord ++ tailWord_469732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469732).length < 2 ^ (prefixWord ++ tailWord_469732).sum := by decide
  have hdescent : baseEnd_469732 < baseStart_469732 := by decide
  rcases family_descends (prefixWord ++ tailWord_469732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469748 : List Nat := [2, 6, 1, 1, 3, 1, 2, 4]
def baseStart_469748 : Nat := 118140960795 + 469748 * 2 ^ 59
def prefixEnd_469748 : Nat := 4983230072969 + 3 ^ 40 * 469748 * 2
def baseEnd_469748 : Nat := 71468595700246916293237

theorem tailTrace_469748 : CollatzResearch.WordTrace tailWord_469748 prefixEnd_469748 71468595700246916293237 := by
  unfold tailWord_469748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566558551095348708172949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11422078068127131610897265 8566558551095348708172949)
  ·
    refine ⟨401557432082594470695607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8566558551095348708172949 401557432082594470695607)
    ·
      refine ⟨602336148123891706043411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401557432082594470695607 602336148123891706043411)
      ·
        refine ⟨903504222185837559065117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602336148123891706043411 903504222185837559065117)
        ·
          refine ⟨338814083319689084649419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 903504222185837559065117 338814083319689084649419)
          ·
            refine ⟨508221124979533626974129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338814083319689084649419 508221124979533626974129)
            ·
              refine ⟨381165843734650220230597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508221124979533626974129 381165843734650220230597)
              ·
                refine ⟨71468595700246916293237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381165843734650220230597 71468595700246916293237)
                ·
                  rfl

theorem cell20_469748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_469748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469748 prefixEnd_469748 := by exact prefixLift 469748
  have htrace : WordTrace (prefixWord ++ tailWord_469748) baseStart_469748 baseEnd_469748 := by
    simpa [prefixWord, tailWord_469748, baseEnd_469748] using wordTrace_append hprefix tailTrace_469748
  have hstable : (prefixWord ++ tailWord_469748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469748).length < 2 ^ (prefixWord ++ tailWord_469748).sum := by decide
  have hdescent : baseEnd_469748 < baseStart_469748 := by decide
  rcases family_descends (prefixWord ++ tailWord_469748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469756 : List Nat := [2, 2, 2, 1, 3, 2, 4, 4]
def baseStart_469756 : Nat := 118140960795 + 469756 * 2 ^ 59
def prefixEnd_469756 : Nat := 4983230072969 + 3 ^ 40 * 469756 * 2
def baseEnd_469756 : Nat := 71469812839576092204337

theorem tailTrace_469756 : CollatzResearch.WordTrace tailWord_469756 prefixEnd_469756 71469812839576092204337 := by
  unfold tailWord_469756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566704443080857391318561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11422272590774476521758081 8566704443080857391318561)
  ·
    refine ⟨6425028332310643043488921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8566704443080857391318561 6425028332310643043488921)
    ·
      refine ⟨4818771249232982282616691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6425028332310643043488921 4818771249232982282616691)
      ·
        refine ⟨7228156873849473423925037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4818771249232982282616691 7228156873849473423925037)
        ·
          refine ⟨2710558827693552533971889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7228156873849473423925037 2710558827693552533971889)
          ·
            refine ⟨2032919120770164400478917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710558827693552533971889 2032919120770164400478917)
            ·
              refine ⟨381172335144405825089797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2032919120770164400478917 381172335144405825089797)
              ·
                refine ⟨71469812839576092204337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381172335144405825089797 71469812839576092204337)
                ·
                  rfl

theorem cell20_469756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_469756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469756 prefixEnd_469756 := by exact prefixLift 469756
  have htrace : WordTrace (prefixWord ++ tailWord_469756) baseStart_469756 baseEnd_469756 := by
    simpa [prefixWord, tailWord_469756, baseEnd_469756] using wordTrace_append hprefix tailTrace_469756
  have hstable : (prefixWord ++ tailWord_469756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469756).length < 2 ^ (prefixWord ++ tailWord_469756).sum := by decide
  have hdescent : baseEnd_469756 < baseStart_469756 := by decide
  rcases family_descends (prefixWord ++ tailWord_469756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469783 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 2]
def baseStart_469783 : Nat := 118140960795 + 469783 * 2 ^ 59
def prefixEnd_469783 : Nat := 4983230072969 + 3 ^ 40 * 469783 * 2
def baseEnd_469783 : Nat := 214421762054436182712901

theorem tailTrace_469783 : CollatzResearch.WordTrace tailWord_469783 prefixEnd_469783 214421762054436182712901 := by
  unfold tailWord_469783
  simp only [CollatzResearch.WordTrace]
  refine ⟨17134393657063898393870003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11422929104709265595913335 17134393657063898393870003)
  ·
    refine ⟨25701590485595847590805005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17134393657063898393870003 25701590485595847590805005)
    ·
      refine ⟨9638096432098442846551877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25701590485595847590805005 9638096432098442846551877)
      ·
        refine ⟨1807143081018458033728477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9638096432098442846551877 1807143081018458033728477)
        ·
          refine ⟨677678655381921762648179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1807143081018458033728477 677678655381921762648179)
          ·
            refine ⟨1016517983072882643972269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677678655381921762648179 1016517983072882643972269)
            ·
              refine ⟨381194243652330991489601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016517983072882643972269 381194243652330991489601)
              ·
                refine ⟨285895682739248243617201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381194243652330991489601 285895682739248243617201)
                ·
                  refine ⟨214421762054436182712901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285895682739248243617201 214421762054436182712901)
                  ·
                    rfl

theorem cell20_469783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 2].length) (baseStart_469783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469783 prefixEnd_469783 := by exact prefixLift 469783
  have htrace : WordTrace (prefixWord ++ tailWord_469783) baseStart_469783 baseEnd_469783 := by
    simpa [prefixWord, tailWord_469783, baseEnd_469783] using wordTrace_append hprefix tailTrace_469783
  have hstable : (prefixWord ++ tailWord_469783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469783).length < 2 ^ (prefixWord ++ tailWord_469783).sum := by decide
  have hdescent : baseEnd_469783 < baseStart_469783 := by decide
  rcases family_descends (prefixWord ++ tailWord_469783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469794 : List Nat := [3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_469794 : Nat := 118140960795 + 469794 * 2 ^ 59
def prefixEnd_469794 : Nat := 4983230072969 + 3 ^ 40 * 469794 * 2
def baseEnd_469794 : Nat := 71475594251389677782063

theorem tailTrace_469794 : CollatzResearch.WordTrace tailWord_469794 prefixEnd_469794 71475594251389677782063 := by
  unfold tailWord_469794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283698715006011818130109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11423196573349364848346957 4283698715006011818130109)
  ·
    refine ⟨1606387018127254431798791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4283698715006011818130109 1606387018127254431798791)
    ·
      refine ⟨2409580527190881647698187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606387018127254431798791 2409580527190881647698187)
      ·
        refine ⟨3614370790786322471547281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409580527190881647698187 3614370790786322471547281)
        ·
          refine ⟨2710778093089741853660461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614370790786322471547281 2710778093089741853660461)
          ·
            refine ⟨1016541784908653195122673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2710778093089741853660461 1016541784908653195122673)
            ·
              refine ⟨762406338681489896342005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016541784908653195122673 762406338681489896342005)
              ·
                refine ⟨71475594251389677782063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762406338681489896342005 71475594251389677782063)
                ·
                  rfl

theorem cell20_469794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_469794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469794 prefixEnd_469794 := by exact prefixLift 469794
  have htrace : WordTrace (prefixWord ++ tailWord_469794) baseStart_469794 baseEnd_469794 := by
    simpa [prefixWord, tailWord_469794, baseEnd_469794] using wordTrace_append hprefix tailTrace_469794
  have hstable : (prefixWord ++ tailWord_469794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469794).length < 2 ^ (prefixWord ++ tailWord_469794).sum := by decide
  have hdescent : baseEnd_469794 < baseStart_469794 := by decide
  rcases family_descends (prefixWord ++ tailWord_469794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469829 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_469829 : Nat := 118140960795 + 469829 * 2 ^ 59
def prefixEnd_469829 : Nat := 4983230072969 + 3 ^ 40 * 469829 * 2
def baseEnd_469829 : Nat := 214442757707864467179379

theorem tailTrace_469829 : CollatzResearch.WordTrace tailWord_469829 prefixEnd_469829 214442757707864467179379 := by
  unfold tailWord_469829
  simp only [CollatzResearch.WordTrace]
  refine ⟨17136071414897248250044541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11424047609931498833363027 17136071414897248250044541)
  ·
    refine ⟨6426026780586468093766703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17136071414897248250044541 6426026780586468093766703)
    ·
      refine ⟨9639040170879702140650055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426026780586468093766703 9639040170879702140650055)
      ·
        refine ⟨14458560256319553210975083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639040170879702140650055 14458560256319553210975083)
        ·
          refine ⟨21687840384479329816462625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14458560256319553210975083 21687840384479329816462625)
          ·
            refine ⟨16265880288359497362346969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21687840384479329816462625 16265880288359497362346969)
            ·
              refine ⟨12199410216269623021760227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16265880288359497362346969 12199410216269623021760227)
              ·
                refine ⟨18299115324404434532640341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12199410216269623021760227 18299115324404434532640341)
                ·
                  refine ⟨214442757707864467179379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18299115324404434532640341 214442757707864467179379)
                  ·
                    rfl

theorem cell20_469829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_469829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469829 prefixEnd_469829 := by exact prefixLift 469829
  have htrace : WordTrace (prefixWord ++ tailWord_469829) baseStart_469829 baseEnd_469829 := by
    simpa [prefixWord, tailWord_469829, baseEnd_469829] using wordTrace_append hprefix tailTrace_469829
  have hstable : (prefixWord ++ tailWord_469829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469829).length < 2 ^ (prefixWord ++ tailWord_469829).sum := by decide
  have hdescent : baseEnd_469829 < baseStart_469829 := by decide
  rcases family_descends (prefixWord ++ tailWord_469829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469867 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_469867 : Nat := 118140960795 + 469867 * 2 ^ 59
def prefixEnd_469867 : Nat := 4983230072969 + 3 ^ 40 * 469867 * 2
def baseEnd_469867 : Nat := 214460101943305223912557

theorem tailTrace_469867 : CollatzResearch.WordTrace tailWord_469867 prefixEnd_469867 214460101943305223912557 := by
  unfold tailWord_469867
  simp only [CollatzResearch.WordTrace]
  refine ⟨17137457388759580739927855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11424971592506387159951903 17137457388759580739927855)
  ·
    refine ⟨25706186083139371109891783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17137457388759580739927855 25706186083139371109891783)
    ·
      refine ⟨38559279124709056664837675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25706186083139371109891783 38559279124709056664837675)
      ·
        refine ⟨57838918687063584997256513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38559279124709056664837675 57838918687063584997256513)
        ·
          refine ⟨43379189015297688747942385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57838918687063584997256513 43379189015297688747942385)
          ·
            refine ⟨32534391761473266560956789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43379189015297688747942385 32534391761473266560956789)
            ·
              refine ⟨3050099227638118740089699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32534391761473266560956789 3050099227638118740089699)
              ·
                refine ⟨4575148841457178110134549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050099227638118740089699 4575148841457178110134549)
                ·
                  refine ⟨214460101943305223912557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4575148841457178110134549 214460101943305223912557)
                  ·
                    rfl

theorem cell20_469867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_469867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469867 prefixEnd_469867 := by exact prefixLift 469867
  have htrace : WordTrace (prefixWord ++ tailWord_469867) baseStart_469867 baseEnd_469867 := by
    simpa [prefixWord, tailWord_469867, baseEnd_469867] using wordTrace_append hprefix tailTrace_469867
  have hstable : (prefixWord ++ tailWord_469867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469867).length < 2 ^ (prefixWord ++ tailWord_469867).sum := by decide
  have hdescent : baseEnd_469867 < baseStart_469867 := by decide
  rcases family_descends (prefixWord ++ tailWord_469867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469943 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_469943 : Nat := 118140960795 + 469943 * 2 ^ 59
def prefixEnd_469943 : Nat := 4983230072969 + 3 ^ 40 * 469943 * 2
def baseEnd_469943 : Nat := 214494790414186737378913

theorem tailTrace_469943 : CollatzResearch.WordTrace tailWord_469943 prefixEnd_469943 214494790414186737378913 := by
  unfold tailWord_469943
  simp only [CollatzResearch.WordTrace]
  refine ⟨17140229336484245719694483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11426819557656163813129655 17140229336484245719694483)
  ·
    refine ⟨25710344004726368579541725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17140229336484245719694483 25710344004726368579541725)
    ·
      refine ⟨9641379001772388217328147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25710344004726368579541725 9641379001772388217328147)
      ·
        refine ⟨14462068502658582325992221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9641379001772388217328147 14462068502658582325992221)
        ·
          refine ⟨5423275688496968372247083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14462068502658582325992221 5423275688496968372247083)
          ·
            refine ⟨8134913532745452558370625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423275688496968372247083 8134913532745452558370625)
            ·
              refine ⟨6101185149559089418777969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8134913532745452558370625 6101185149559089418777969)
              ·
                refine ⟨4575888862169317064083477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6101185149559089418777969 4575888862169317064083477)
                ·
                  refine ⟨214494790414186737378913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4575888862169317064083477 214494790414186737378913)
                  ·
                    rfl

theorem cell20_469943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_469943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469943 prefixEnd_469943 := by exact prefixLift 469943
  have htrace : WordTrace (prefixWord ++ tailWord_469943) baseStart_469943 baseEnd_469943 := by
    simpa [prefixWord, tailWord_469943, baseEnd_469943] using wordTrace_append hprefix tailTrace_469943
  have hstable : (prefixWord ++ tailWord_469943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469943).length < 2 ^ (prefixWord ++ tailWord_469943).sum := by decide
  have hdescent : baseEnd_469943 < baseStart_469943 := by decide
  rcases family_descends (prefixWord ++ tailWord_469943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469967 : List Nat := [1, 1, 2, 1, 1, 7, 2, 5]
def baseStart_469967 : Nat := 118140960795 + 469967 * 2 ^ 59
def prefixEnd_469967 : Nat := 4983230072969 + 3 ^ 40 * 469967 * 2
def baseEnd_469967 : Nat := 71501914889383106859605

theorem tailTrace_469967 : CollatzResearch.WordTrace tailWord_469967 prefixEnd_469967 71501914889383106859605 := by
  unfold tailWord_469967
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141104688397297818568155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11427403125598198545712103 17141104688397297818568155)
  ·
    refine ⟨25711657032595946727852233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17141104688397297818568155 25711657032595946727852233)
    ·
      refine ⟨19283742774446960045889175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25711657032595946727852233 19283742774446960045889175)
      ·
        refine ⟨28925614161670440068833763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19283742774446960045889175 28925614161670440068833763)
        ·
          refine ⟨43388421242505660103250645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28925614161670440068833763 43388421242505660103250645)
          ·
            refine ⟨1016916122871226408669937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43388421242505660103250645 1016916122871226408669937)
            ·
              refine ⟨762687092153419806502453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016916122871226408669937 762687092153419806502453)
              ·
                refine ⟨71501914889383106859605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762687092153419806502453 71501914889383106859605)
                ·
                  rfl

theorem cell20_469967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_469967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469967 prefixEnd_469967 := by exact prefixLift 469967
  have htrace : WordTrace (prefixWord ++ tailWord_469967) baseStart_469967 baseEnd_469967 := by
    simpa [prefixWord, tailWord_469967, baseEnd_469967] using wordTrace_append hprefix tailTrace_469967
  have hstable : (prefixWord ++ tailWord_469967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469967).length < 2 ^ (prefixWord ++ tailWord_469967).sum := by decide
  have hdescent : baseEnd_469967 < baseStart_469967 := by decide
  rcases family_descends (prefixWord ++ tailWord_469967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469970 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_469970 : Nat := 118140960795 + 469970 * 2 ^ 59
def prefixEnd_469970 : Nat := 4983230072969 + 3 ^ 40 * 469970 * 2
def baseEnd_469970 : Nat := 214507113949894643478803

theorem tailTrace_469970 : CollatzResearch.WordTrace tailWord_469970 prefixEnd_469970 214507113949894643478803 := by
  unfold tailWord_469970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285303526846607332731841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11427476071590952887284909 4285303526846607332731841)
  ·
    refine ⟨3213977645134955499548881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4285303526846607332731841 3213977645134955499548881)
    ·
      refine ⟨2410483233851216624661661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3213977645134955499548881 2410483233851216624661661)
      ·
        refine ⟨903931212694206234248123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2410483233851216624661661 903931212694206234248123)
        ·
          refine ⟨1355896819041309351372185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903931212694206234248123 1355896819041309351372185)
          ·
            refine ⟨1016922614280982013529139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355896819041309351372185 1016922614280982013529139)
            ·
              refine ⟨1525383921421473020293709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016922614280982013529139 1525383921421473020293709)
              ·
                refine ⟨572018970533052382610141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525383921421473020293709 572018970533052382610141)
                ·
                  refine ⟨214507113949894643478803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572018970533052382610141 214507113949894643478803)
                  ·
                    rfl

theorem cell20_469970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_469970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_469970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_469970 prefixEnd_469970 := by exact prefixLift 469970
  have htrace : WordTrace (prefixWord ++ tailWord_469970) baseStart_469970 baseEnd_469970 := by
    simpa [prefixWord, tailWord_469970, baseEnd_469970] using wordTrace_append hprefix tailTrace_469970
  have hstable : (prefixWord ++ tailWord_469970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469970).length < 2 ^ (prefixWord ++ tailWord_469970).sum := by decide
  have hdescent : baseEnd_469970 < baseStart_469970 := by decide
  rcases family_descends (prefixWord ++ tailWord_469970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470018 : List Nat := [3, 4, 1, 3, 1, 2, 1, 5]
def baseStart_470018 : Nat := 118140960795 + 470018 * 2 ^ 59
def prefixEnd_470018 : Nat := 4983230072969 + 3 ^ 40 * 470018 * 2
def baseEnd_470018 : Nat := 71509674152606603292869

theorem tailTrace_470018 : CollatzResearch.WordTrace tailWord_470018 prefixEnd_470018 71509674152606603292869 := by
  unfold tailWord_470018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285741202803133382168677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11428643207475022352449805 4285741202803133382168677)
  ·
    refine ⟨803576475525587509156627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4285741202803133382168677 803576475525587509156627)
    ·
      refine ⟨1205364713288381263734941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803576475525587509156627 1205364713288381263734941)
      ·
        refine ⟨452011767483142973900603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1205364713288381263734941 452011767483142973900603)
        ·
          refine ⟨678017651224714460850905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452011767483142973900603 678017651224714460850905)
          ·
            refine ⟨508513238418535845638179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678017651224714460850905 508513238418535845638179)
            ·
              refine ⟨762769857627803768457269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508513238418535845638179 762769857627803768457269)
              ·
                refine ⟨71509674152606603292869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762769857627803768457269 71509674152606603292869)
                ·
                  rfl

theorem cell20_470018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_470018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470018 prefixEnd_470018 := by exact prefixLift 470018
  have htrace : WordTrace (prefixWord ++ tailWord_470018) baseStart_470018 baseEnd_470018 := by
    simpa [prefixWord, tailWord_470018, baseEnd_470018] using wordTrace_append hprefix tailTrace_470018
  have hstable : (prefixWord ++ tailWord_470018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470018).length < 2 ^ (prefixWord ++ tailWord_470018).sum := by decide
  have hdescent : baseEnd_470018 < baseStart_470018 := by decide
  rcases family_descends (prefixWord ++ tailWord_470018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470053 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 2]
def baseStart_470053 : Nat := 118140960795 + 470053 * 2 ^ 59
def prefixEnd_470053 : Nat := 4983230072969 + 3 ^ 40 * 470053 * 2
def baseEnd_470053 : Nat := 214544997411515243711797

theorem tailTrace_470053 : CollatzResearch.WordTrace tailWord_470053 prefixEnd_470053 214544997411515243711797 := by
  unfold tailWord_470053
  simp only [CollatzResearch.WordTrace]
  refine ⟨17144241366085734506198813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11429494244057156337465875 17144241366085734506198813)
  ·
    refine ⟨6429090512282150439824555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17144241366085734506198813 6429090512282150439824555)
    ·
      refine ⟨9643635768423225659736833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429090512282150439824555 9643635768423225659736833)
      ·
        refine ⟨7232726826317419244802625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9643635768423225659736833 7232726826317419244802625)
        ·
          refine ⟨5424545119738064433601969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7232726826317419244802625 5424545119738064433601969)
          ·
            refine ⟨4068408839803548325201477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5424545119738064433601969 4068408839803548325201477)
            ·
              refine ⟨762826657463165310975277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4068408839803548325201477 762826657463165310975277)
              ·
                refine ⟨286059996548686991615729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762826657463165310975277 286059996548686991615729)
                ·
                  refine ⟨214544997411515243711797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286059996548686991615729 214544997411515243711797)
                  ·
                    rfl

theorem cell20_470053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_470053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470053 prefixEnd_470053 := by exact prefixLift 470053
  have htrace : WordTrace (prefixWord ++ tailWord_470053) baseStart_470053 baseEnd_470053 := by
    simpa [prefixWord, tailWord_470053, baseEnd_470053] using wordTrace_append hprefix tailTrace_470053
  have hstable : (prefixWord ++ tailWord_470053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470053).length < 2 ^ (prefixWord ++ tailWord_470053).sum := by decide
  have hdescent : baseEnd_470053 < baseStart_470053 := by decide
  rcases family_descends (prefixWord ++ tailWord_470053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470064 : List Nat := [2, 1, 1, 1, 2, 4, 9]
def baseStart_470064 : Nat := 118140960795 + 470064 * 2 ^ 59
def prefixEnd_470064 : Nat := 4983230072969 + 3 ^ 40 * 470064 * 2
def baseEnd_470064 : Nat := 23838890901249788260565

theorem tailTrace_470064 : CollatzResearch.WordTrace tailWord_470064 prefixEnd_470064 23838890901249788260565 := by
  unfold tailWord_470064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572321284522941692424623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11429761712697255589899497 8572321284522941692424623)
  ·
    refine ⟨12858481926784412538636935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8572321284522941692424623 12858481926784412538636935)
    ·
      refine ⟨19287722890176618807955403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12858481926784412538636935 19287722890176618807955403)
      ·
        refine ⟨28931584335264928211933105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19287722890176618807955403 28931584335264928211933105)
        ·
          refine ⟨21698688251448696158949829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28931584335264928211933105 21698688251448696158949829)
          ·
            refine ⟨4068504047146630529803093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21698688251448696158949829 4068504047146630529803093)
            ·
              refine ⟨23838890901249788260565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4068504047146630529803093 23838890901249788260565)
              ·
                rfl

theorem cell20_470064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_470064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470064 prefixEnd_470064 := by exact prefixLift 470064
  have htrace : WordTrace (prefixWord ++ tailWord_470064) baseStart_470064 baseEnd_470064 := by
    simpa [prefixWord, tailWord_470064, baseEnd_470064] using wordTrace_append hprefix tailTrace_470064
  have hstable : (prefixWord ++ tailWord_470064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470064).length < 2 ^ (prefixWord ++ tailWord_470064).sum := by decide
  have hdescent : baseEnd_470064 < baseStart_470064 := by decide
  rcases family_descends (prefixWord ++ tailWord_470064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470070 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_470070 : Nat := 118140960795 + 470070 * 2 ^ 59
def prefixEnd_470070 : Nat := 4983230072969 + 3 ^ 40 * 470070 * 2
def baseEnd_470070 : Nat := 214552756674738740145061

theorem tailTrace_470070 : CollatzResearch.WordTrace tailWord_470070 prefixEnd_470070 214552756674738740145061 := by
  unfold tailWord_470070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071553837939009150597979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11429907604682764273045109 1071553837939009150597979)
  ·
    refine ⟨1607330756908513725896969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1071553837939009150597979 1607330756908513725896969)
    ·
      refine ⟨1205498067681385294422727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1607330756908513725896969 1205498067681385294422727)
      ·
        refine ⟨1808247101522077941634091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205498067681385294422727 1808247101522077941634091)
        ·
          refine ⟨2712370652283116912451137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808247101522077941634091 2712370652283116912451137)
          ·
            refine ⟨2034277989212337684338353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712370652283116912451137 2034277989212337684338353)
            ·
              refine ⟨1525708491909253263253765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034277989212337684338353 1525708491909253263253765)
              ·
                refine ⟨286070342232984986860081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1525708491909253263253765 286070342232984986860081)
                ·
                  refine ⟨214552756674738740145061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286070342232984986860081 214552756674738740145061)
                  ·
                    rfl

theorem cell20_470070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_470070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470070 prefixEnd_470070 := by exact prefixLift 470070
  have htrace : WordTrace (prefixWord ++ tailWord_470070) baseStart_470070 baseEnd_470070 := by
    simpa [prefixWord, tailWord_470070, baseEnd_470070] using wordTrace_append hprefix tailTrace_470070
  have hstable : (prefixWord ++ tailWord_470070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470070).length < 2 ^ (prefixWord ++ tailWord_470070).sum := by decide
  have hdescent : baseEnd_470070 < baseStart_470070 := by decide
  rcases family_descends (prefixWord ++ tailWord_470070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470098 : List Nat := [3, 2, 2, 1, 3, 1, 4, 4]
def baseStart_470098 : Nat := 118140960795 + 470098 * 2 ^ 59
def prefixEnd_470098 : Nat := 4983230072969 + 3 ^ 40 * 470098 * 2
def baseEnd_470098 : Nat := 71521845545898362403871

theorem tailTrace_470098 : CollatzResearch.WordTrace tailWord_470098 prefixEnd_470098 71521845545898362403871 := by
  unfold tailWord_470098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286470662730676797896737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11430588433948471461057965 4286470662730676797896737)
  ·
    refine ⟨3214852997048007598422553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4286470662730676797896737 3214852997048007598422553)
    ·
      refine ⟨2411139747786005698816915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3214852997048007598422553 2411139747786005698816915)
      ·
        refine ⟨3616709621679008548225373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411139747786005698816915 3616709621679008548225373)
        ·
          refine ⟨1356266108129628205584515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3616709621679008548225373 1356266108129628205584515)
          ·
            refine ⟨2034399162194442308376773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356266108129628205584515 2034399162194442308376773)
            ·
              refine ⟨381449842911457932820645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2034399162194442308376773 381449842911457932820645)
              ·
                refine ⟨71521845545898362403871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381449842911457932820645 71521845545898362403871)
                ·
                  rfl

theorem cell20_470098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_470098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470098 prefixEnd_470098 := by exact prefixLift 470098
  have htrace : WordTrace (prefixWord ++ tailWord_470098) baseStart_470098 baseEnd_470098 := by
    simpa [prefixWord, tailWord_470098, baseEnd_470098] using wordTrace_append hprefix tailTrace_470098
  have hstable : (prefixWord ++ tailWord_470098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470098).length < 2 ^ (prefixWord ++ tailWord_470098).sum := by decide
  have hdescent : baseEnd_470098 < baseStart_470098 := by decide
  rcases family_descends (prefixWord ++ tailWord_470098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470119 : List Nat := [1, 1, 5, 1, 1, 5, 6]
def baseStart_470119 : Nat := 118140960795 + 470119 * 2 ^ 59
def prefixEnd_470119 : Nat := 4983230072969 + 3 ^ 40 * 470119 * 2
def baseEnd_470119 : Nat := 23841680178879149723503

theorem tailTrace_470119 : CollatzResearch.WordTrace tailWord_470119 prefixEnd_470119 23841680178879149723503 := by
  unfold tailWord_470119
  simp only [CollatzResearch.WordTrace]
  refine ⟨17146648583846627778101411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11431099055897751852067607 17146648583846627778101411)
  ·
    refine ⟨25719972875769941667152117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17146648583846627778101411 25719972875769941667152117)
    ·
      refine ⟨2411247457103432031295511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25719972875769941667152117 2411247457103432031295511)
      ·
        refine ⟨3616871185655148046943267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411247457103432031295511 3616871185655148046943267)
        ·
          refine ⟨5425306778482722070414901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616871185655148046943267 5425306778482722070414901)
          ·
            refine ⟨508622510482755194101397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5425306778482722070414901 508622510482755194101397)
            ·
              refine ⟨23841680178879149723503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 508622510482755194101397 23841680178879149723503)
              ·
                rfl

theorem cell20_470119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_470119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470119 prefixEnd_470119 := by exact prefixLift 470119
  have htrace : WordTrace (prefixWord ++ tailWord_470119) baseStart_470119 baseEnd_470119 := by
    simpa [prefixWord, tailWord_470119, baseEnd_470119] using wordTrace_append hprefix tailTrace_470119
  have hstable : (prefixWord ++ tailWord_470119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470119).length < 2 ^ (prefixWord ++ tailWord_470119).sum := by decide
  have hdescent : baseEnd_470119 < baseStart_470119 := by decide
  rcases family_descends (prefixWord ++ tailWord_470119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470181 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_470181 : Nat := 118140960795 + 470181 * 2 ^ 59
def prefixEnd_470181 : Nat := 4983230072969 + 3 ^ 40 * 470181 * 2
def baseEnd_470181 : Nat := 214603420099315687444607

theorem tailTrace_470181 : CollatzResearch.WordTrace tailWord_470181 prefixEnd_470181 214603420099315687444607 := by
  unfold tailWord_470181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17148909909622012366858397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11432606606414674911238931 17148909909622012366858397)
  ·
    refine ⟨6430841216108254637571899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17148909909622012366858397 6430841216108254637571899)
    ·
      refine ⟨9646261824162381956357849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6430841216108254637571899 9646261824162381956357849)
      ·
        refine ⟨7234696368121786467268387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9646261824162381956357849 7234696368121786467268387)
        ·
          refine ⟨10852044552182679700902581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234696368121786467268387 10852044552182679700902581)
          ·
            refine ⟨1017379176767126221959617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10852044552182679700902581 1017379176767126221959617)
            ·
              refine ⟨763034382575344666469713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017379176767126221959617 763034382575344666469713)
              ·
                refine ⟨572275786931508499852285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763034382575344666469713 572275786931508499852285)
                ·
                  refine ⟨214603420099315687444607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572275786931508499852285 214603420099315687444607)
                  ·
                    rfl

theorem cell20_470181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_470181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470181 prefixEnd_470181 := by exact prefixLift 470181
  have htrace : WordTrace (prefixWord ++ tailWord_470181) baseStart_470181 baseEnd_470181 := by
    simpa [prefixWord, tailWord_470181, baseEnd_470181] using wordTrace_append hprefix tailTrace_470181
  have hstable : (prefixWord ++ tailWord_470181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470181).length < 2 ^ (prefixWord ++ tailWord_470181).sum := by decide
  have hdescent : baseEnd_470181 < baseStart_470181 := by decide
  rcases family_descends (prefixWord ++ tailWord_470181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470216 : List Nat := [2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_470216 : Nat := 118140960795 + 470216 * 2 ^ 59
def prefixEnd_470216 : Nat := 4983230072969 + 3 ^ 40 * 470216 * 2
def baseEnd_470216 : Nat := 71539798351003707092599

theorem tailTrace_470216 : CollatzResearch.WordTrace tailWord_470216 prefixEnd_470216 71539798351003707092599 := by
  unfold tailWord_470216
  simp only [CollatzResearch.WordTrace]
  refine ⟨8575093232247606672191251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11433457642996808896255001 8575093232247606672191251)
  ·
    refine ⟨12862639848371410008286877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8575093232247606672191251 12862639848371410008286877)
    ·
      refine ⟨4823489943139278753107579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12862639848371410008286877 4823489943139278753107579)
      ·
        refine ⟨7235234914708918129661369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823489943139278753107579 7235234914708918129661369)
        ·
          refine ⟨5426426186031688597246027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235234914708918129661369 5426426186031688597246027)
          ·
            refine ⟨8139639279047532895869041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426426186031688597246027 8139639279047532895869041)
            ·
              refine ⟨6104729459285649671901781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8139639279047532895869041 6104729459285649671901781)
              ·
                refine ⟨71539798351003707092599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6104729459285649671901781 71539798351003707092599)
                ·
                  rfl

theorem cell20_470216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_470216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470216 prefixEnd_470216 := by exact prefixLift 470216
  have htrace : WordTrace (prefixWord ++ tailWord_470216) baseStart_470216 baseEnd_470216 := by
    simpa [prefixWord, tailWord_470216, baseEnd_470216] using wordTrace_append hprefix tailTrace_470216
  have hstable : (prefixWord ++ tailWord_470216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470216).length < 2 ^ (prefixWord ++ tailWord_470216).sum := by decide
  have hdescent : baseEnd_470216 < baseStart_470216 := by decide
  rcases family_descends (prefixWord ++ tailWord_470216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470222 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_470222 : Nat := 118140960795 + 470222 * 2 ^ 59
def prefixEnd_470222 : Nat := 4983230072969 + 3 ^ 40 * 470222 * 2
def baseEnd_470222 : Nat := 214622133616501767077773

theorem tailTrace_470222 : CollatzResearch.WordTrace tailWord_470222 prefixEnd_470222 214622133616501767077773 := by
  unfold tailWord_470222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143800662809184546137615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11433603534982317579400613 2143800662809184546137615)
  ·
    refine ⟨3215700994213776819206423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2143800662809184546137615 3215700994213776819206423)
    ·
      refine ⟨4823551491320665228809635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215700994213776819206423 4823551491320665228809635)
      ·
        refine ⟨7235327236980997843214453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823551491320665228809635 7235327236980997843214453)
        ·
          refine ⟨678311928466968547801355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7235327236980997843214453 678311928466968547801355)
          ·
            refine ⟨1017467892700452821702033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678311928466968547801355 1017467892700452821702033)
            ·
              refine ⟨763100919525339616276525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017467892700452821702033 763100919525339616276525)
              ·
                refine ⟨286162844822002356103697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 763100919525339616276525 286162844822002356103697)
                ·
                  refine ⟨214622133616501767077773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286162844822002356103697 214622133616501767077773)
                  ·
                    rfl

theorem cell20_470222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_470222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470222 prefixEnd_470222 := by exact prefixLift 470222
  have htrace : WordTrace (prefixWord ++ tailWord_470222) baseStart_470222 baseEnd_470222 := by
    simpa [prefixWord, tailWord_470222, baseEnd_470222] using wordTrace_append hprefix tailTrace_470222
  have hstable : (prefixWord ++ tailWord_470222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470222).length < 2 ^ (prefixWord ++ tailWord_470222).sum := by decide
  have hdescent : baseEnd_470222 < baseStart_470222 := by decide
  rcases family_descends (prefixWord ++ tailWord_470222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470240 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_470240 : Nat := 118140960795 + 470240 * 2 ^ 59
def prefixEnd_470240 : Nat := 4983230072969 + 3 ^ 40 * 470240 * 2
def baseEnd_470240 : Nat := 214630349306973704477699

theorem tailTrace_470240 : CollatzResearch.WordTrace tailWord_470240 prefixEnd_470240 214630349306973704477699 := by
  unfold tailWord_470240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8575530908204132721628087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11434041210938843628837449 8575530908204132721628087)
  ·
    refine ⟨12863296362306199082442131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8575530908204132721628087 12863296362306199082442131)
    ·
      refine ⟨19294944543459298623663197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12863296362306199082442131 19294944543459298623663197)
      ·
        refine ⟨7235604203797236983873699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19294944543459298623663197 7235604203797236983873699)
        ·
          refine ⟨10853406305695855475810549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235604203797236983873699 10853406305695855475810549)
          ·
            refine ⟨1017506841158986450857239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10853406305695855475810549 1017506841158986450857239)
            ·
              refine ⟨1526260261738479676285859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017506841158986450857239 1526260261738479676285859)
              ·
                refine ⟨2289390392607719514428789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526260261738479676285859 2289390392607719514428789)
                ·
                  refine ⟨214630349306973704477699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2289390392607719514428789 214630349306973704477699)
                  ·
                    rfl

theorem cell20_470240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_470240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470240 prefixEnd_470240 := by exact prefixLift 470240
  have htrace : WordTrace (prefixWord ++ tailWord_470240) baseStart_470240 baseEnd_470240 := by
    simpa [prefixWord, tailWord_470240, baseEnd_470240] using wordTrace_append hprefix tailTrace_470240
  have hstable : (prefixWord ++ tailWord_470240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470240).length < 2 ^ (prefixWord ++ tailWord_470240).sum := by decide
  have hdescent : baseEnd_470240 < baseStart_470240 := by decide
  rcases family_descends (prefixWord ++ tailWord_470240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470271 : List Nat := [1, 1, 2, 2, 1, 5, 4, 4]
def baseStart_470271 : Nat := 118140960795 + 470271 * 2 ^ 59
def prefixEnd_470271 : Nat := 4983230072969 + 3 ^ 40 * 470271 * 2
def baseEnd_470271 : Nat := 71548166183891791481413

theorem tailTrace_470271 : CollatzResearch.WordTrace tailWord_470271 prefixEnd_470271 71548166183891791481413 := by
  unfold tailWord_470271
  simp only [CollatzResearch.WordTrace]
  refine ⟨17152192479295957737634667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11434794986197305158423111 17152192479295957737634667)
  ·
    refine ⟨25728288718943936606452001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17152192479295957737634667 25728288718943936606452001)
    ·
      refine ⟨19296216539207952454839001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25728288718943936606452001 19296216539207952454839001)
      ·
        refine ⟨14472162404405964341129251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19296216539207952454839001 14472162404405964341129251)
        ·
          refine ⟨21708243606608946511693877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14472162404405964341129251 21708243606608946511693877)
          ·
            refine ⟨2035147838119588735471301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21708243606608946511693877 2035147838119588735471301)
            ·
              refine ⟨381590219647422887900869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2035147838119588735471301 381590219647422887900869)
              ·
                refine ⟨71548166183891791481413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381590219647422887900869 71548166183891791481413)
                ·
                  rfl

theorem cell20_470271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_470271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470271 prefixEnd_470271 := by exact prefixLift 470271
  have htrace : WordTrace (prefixWord ++ tailWord_470271) baseStart_470271 baseEnd_470271 := by
    simpa [prefixWord, tailWord_470271, baseEnd_470271] using wordTrace_append hprefix tailTrace_470271
  have hstable : (prefixWord ++ tailWord_470271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470271).length < 2 ^ (prefixWord ++ tailWord_470271).sum := by decide
  have hdescent : baseEnd_470271 < baseStart_470271 := by decide
  rcases family_descends (prefixWord ++ tailWord_470271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470298 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_470298 : Nat := 118140960795 + 470298 * 2 ^ 59
def prefixEnd_470298 : Nat := 4983230072969 + 3 ^ 40 * 470298 * 2
def baseEnd_470298 : Nat := 214656822087383280544129

theorem tailTrace_470298 : CollatzResearch.WordTrace tailWord_470298 prefixEnd_470298 214656822087383280544129 := by
  unfold tailWord_470298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288294312549535337216887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11435451500132094232578365 4288294312549535337216887)
  ·
    refine ⟨6432441468824303005825331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288294312549535337216887 6432441468824303005825331)
    ·
      refine ⟨9648662203236454508737997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432441468824303005825331 9648662203236454508737997)
      ·
        refine ⟨3618248326213670440776749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9648662203236454508737997 3618248326213670440776749)
        ·
          refine ⟨1356843122330126415291281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3618248326213670440776749 1356843122330126415291281)
          ·
            refine ⟨1017632341747594811468461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356843122330126415291281 1017632341747594811468461)
            ·
              refine ⟨381612128155348054300673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1017632341747594811468461 381612128155348054300673)
              ·
                refine ⟨286209096116511040725505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381612128155348054300673 286209096116511040725505)
                ·
                  refine ⟨214656822087383280544129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286209096116511040725505 214656822087383280544129)
                  ·
                    rfl

theorem cell20_470298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_470298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470298 prefixEnd_470298 := by exact prefixLift 470298
  have htrace : WordTrace (prefixWord ++ tailWord_470298) baseStart_470298 baseEnd_470298 := by
    simpa [prefixWord, tailWord_470298, baseEnd_470298] using wordTrace_append hprefix tailTrace_470298
  have hstable : (prefixWord ++ tailWord_470298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470298).length < 2 ^ (prefixWord ++ tailWord_470298).sum := by decide
  have hdescent : baseEnd_470298 < baseStart_470298 := by decide
  rcases family_descends (prefixWord ++ tailWord_470298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470309 : List Nat := [1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_470309 : Nat := 118140960795 + 470309 * 2 ^ 59
def prefixEnd_470309 : Nat := 4983230072969 + 3 ^ 40 * 470309 * 2
def baseEnd_470309 : Nat := 71553947595705377059139

theorem tailTrace_470309 : CollatzResearch.WordTrace tailWord_470309 prefixEnd_470309 71553947595705377059139 := by
  unfold tailWord_470309
  simp only [CollatzResearch.WordTrace]
  refine ⟨17153578453158290227517981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11435718968772193485011987 17153578453158290227517981)
  ·
    refine ⟨6432591919934358835319243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17153578453158290227517981 6432591919934358835319243)
    ·
      refine ⟨9648887879901538252978865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432591919934358835319243 9648887879901538252978865)
      ·
        refine ⟨7236665909926153689734149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9648887879901538252978865 7236665909926153689734149)
        ·
          refine ⟨1356874858111153816825153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7236665909926153689734149 1356874858111153816825153)
          ·
            refine ⟨1017656143583365362618865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356874858111153816825153 1017656143583365362618865)
            ·
              refine ⟨763242107687524021964149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017656143583365362618865 763242107687524021964149)
              ·
                refine ⟨71553947595705377059139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 763242107687524021964149 71553947595705377059139)
                ·
                  rfl

theorem cell20_470309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_470309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470309 prefixEnd_470309 := by exact prefixLift 470309
  have htrace : WordTrace (prefixWord ++ tailWord_470309) baseStart_470309 baseEnd_470309 := by
    simpa [prefixWord, tailWord_470309, baseEnd_470309] using wordTrace_append hprefix tailTrace_470309
  have hstable : (prefixWord ++ tailWord_470309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470309).length < 2 ^ (prefixWord ++ tailWord_470309).sum := by decide
  have hdescent : baseEnd_470309 < baseStart_470309 := by decide
  rcases family_descends (prefixWord ++ tailWord_470309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470312 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_470312 : Nat := 118140960795 + 470312 * 2 ^ 59
def prefixEnd_470312 : Nat := 4983230072969 + 3 ^ 40 * 470312 * 2
def baseEnd_470312 : Nat := 214663212068861454077405

theorem tailTrace_470312 : CollatzResearch.WordTrace tailWord_470312 prefixEnd_470312 214663212068861454077405 := by
  unfold tailWord_470312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576843936073710869938595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11435791914764947826584793 8576843936073710869938595)
  ·
    refine ⟨12865265904110566304907893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8576843936073710869938595 12865265904110566304907893)
    ·
      refine ⟨1206118678510365591085115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12865265904110566304907893 1206118678510365591085115)
      ·
        refine ⟨1809178017765548386627673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206118678510365591085115 1809178017765548386627673)
        ·
          refine ⟨1356883513324161289970755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1809178017765548386627673 1356883513324161289970755)
          ·
            refine ⟨2035325269986241934956133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356883513324161289970755 2035325269986241934956133)
            ·
              refine ⟨381623488122420362804275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2035325269986241934956133 381623488122420362804275)
              ·
                refine ⟨572435232183630544206413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381623488122420362804275 572435232183630544206413)
                ·
                  refine ⟨214663212068861454077405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572435232183630544206413 214663212068861454077405)
                  ·
                    rfl

theorem cell20_470312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_470312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470312 prefixEnd_470312 := by exact prefixLift 470312
  have htrace : WordTrace (prefixWord ++ tailWord_470312) baseStart_470312 baseEnd_470312 := by
    simpa [prefixWord, tailWord_470312, baseEnd_470312] using wordTrace_append hprefix tailTrace_470312
  have hstable : (prefixWord ++ tailWord_470312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470312).length < 2 ^ (prefixWord ++ tailWord_470312).sum := by decide
  have hdescent : baseEnd_470312 < baseStart_470312 := by decide
  rcases family_descends (prefixWord ++ tailWord_470312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470330 : List Nat := [3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_470330 : Nat := 118140960795 + 470330 * 2 ^ 59
def prefixEnd_470330 : Nat := 4983230072969 + 3 ^ 40 * 470330 * 2
def baseEnd_470330 : Nat := 71557142586444463825777

theorem tailTrace_470330 : CollatzResearch.WordTrace tailWord_470330 prefixEnd_470330 71557142586444463825777 := by
  unfold tailWord_470330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288586096520552703508111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11436229590721473876021629 4288586096520552703508111)
  ·
    refine ⟨6432879144780829055262167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288586096520552703508111 6432879144780829055262167)
    ·
      refine ⟨9649318717171243582893251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432879144780829055262167 9649318717171243582893251)
      ·
        refine ⟨14473978075756865374339877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9649318717171243582893251 14473978075756865374339877)
        ·
          refine ⟨2713870889204412257688727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14473978075756865374339877 2713870889204412257688727)
          ·
            refine ⟨4070806333806618386533091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2713870889204412257688727 4070806333806618386533091)
            ·
              refine ⟨6106209500709927579799637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070806333806618386533091 6106209500709927579799637)
              ·
                refine ⟨71557142586444463825777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6106209500709927579799637 71557142586444463825777)
                ·
                  rfl

theorem cell20_470330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_470330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470330 prefixEnd_470330 := by exact prefixLift 470330
  have htrace : WordTrace (prefixWord ++ tailWord_470330) baseStart_470330 baseEnd_470330 := by
    simpa [prefixWord, tailWord_470330, baseEnd_470330] using wordTrace_append hprefix tailTrace_470330
  have hstable : (prefixWord ++ tailWord_470330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470330).length < 2 ^ (prefixWord ++ tailWord_470330).sum := by decide
  have hdescent : baseEnd_470330 < baseStart_470330 := by decide
  rcases family_descends (prefixWord ++ tailWord_470330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470349 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 2]
def baseStart_470349 : Nat := 118140960795 + 470349 * 2 ^ 59
def prefixEnd_470349 : Nat := 4983230072969 + 3 ^ 40 * 470349 * 2
def baseEnd_470349 : Nat := 214680099877053769843921

theorem tailTrace_470349 : CollatzResearch.WordTrace tailWord_470349 prefixEnd_470349 214680099877053769843921 := by
  unfold tailWord_470349
  simp only [CollatzResearch.WordTrace]
  refine ⟨17155037373013377058974101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11436691582008918039316067 17155037373013377058974101)
  ·
    refine ⟨804142376860002049639411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17155037373013377058974101 804142376860002049639411)
    ·
      refine ⟨1206213565290003074459117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804142376860002049639411 1206213565290003074459117)
      ·
        refine ⟨452330086983751152922169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1206213565290003074459117 452330086983751152922169)
        ·
          refine ⟨339247565237813364691627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452330086983751152922169 339247565237813364691627)
          ·
            refine ⟨508871347856720047037441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339247565237813364691627 508871347856720047037441)
            ·
              refine ⟨381653510892540035278081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508871347856720047037441 381653510892540035278081)
              ·
                refine ⟨286240133169405026458561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381653510892540035278081 286240133169405026458561)
                ·
                  refine ⟨214680099877053769843921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286240133169405026458561 214680099877053769843921)
                  ·
                    rfl

theorem cell20_470349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_470349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470349 prefixEnd_470349 := by exact prefixLift 470349
  have htrace : WordTrace (prefixWord ++ tailWord_470349) baseStart_470349 baseEnd_470349 := by
    simpa [prefixWord, tailWord_470349, baseEnd_470349] using wordTrace_append hprefix tailTrace_470349
  have hstable : (prefixWord ++ tailWord_470349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470349).length < 2 ^ (prefixWord ++ tailWord_470349).sum := by decide
  have hdescent : baseEnd_470349 < baseStart_470349 := by decide
  rcases family_descends (prefixWord ++ tailWord_470349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470357 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 2]
def baseStart_470357 : Nat := 118140960795 + 470357 * 2 ^ 59
def prefixEnd_470357 : Nat := 4983230072969 + 3 ^ 40 * 470357 * 2
def baseEnd_470357 : Nat := 214683751295041297577221

theorem tailTrace_470357 : CollatzResearch.WordTrace tailWord_470357 prefixEnd_470357 214683751295041297577221 := by
  unfold tailWord_470357
  simp only [CollatzResearch.WordTrace]
  refine ⟨17155329156984394425265325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11436886104656262950176883 17155329156984394425265325)
  ·
    refine ⟨6433248433869147909474497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17155329156984394425265325 6433248433869147909474497)
    ·
      refine ⟨4824936325401860932105873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6433248433869147909474497 4824936325401860932105873)
      ·
        refine ⟨3618702244051395699079405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4824936325401860932105873 3618702244051395699079405)
        ·
          refine ⟨1357013341519273387154777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3618702244051395699079405 1357013341519273387154777)
          ·
            refine ⟨1017760006139455040366083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1357013341519273387154777 1017760006139455040366083)
            ·
              refine ⟨1526640009209182560549125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017760006139455040366083 1526640009209182560549125)
              ·
                refine ⟨286245001726721730102961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1526640009209182560549125 286245001726721730102961)
                ·
                  refine ⟨214683751295041297577221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286245001726721730102961 214683751295041297577221)
                  ·
                    rfl

theorem cell20_470357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_470357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470357 prefixEnd_470357 := by exact prefixLift 470357
  have htrace : WordTrace (prefixWord ++ tailWord_470357) baseStart_470357 baseEnd_470357 := by
    simpa [prefixWord, tailWord_470357, baseEnd_470357] using wordTrace_append hprefix tailTrace_470357
  have hstable : (prefixWord ++ tailWord_470357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470357).length < 2 ^ (prefixWord ++ tailWord_470357).sum := by decide
  have hdescent : baseEnd_470357 < baseStart_470357 := by decide
  rcases family_descends (prefixWord ++ tailWord_470357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470402 : List Nat := [3, 4, 2, 1, 1, 2, 7]
def baseStart_470402 : Nat := 118140960795 + 470402 * 2 ^ 59
def prefixEnd_470402 : Nat := 4983230072969 + 3 ^ 40 * 470402 * 2
def baseEnd_470402 : Nat := 23856032280135682341893

theorem tailTrace_470402 : CollatzResearch.WordTrace tailWord_470402 prefixEnd_470402 23856032280135682341893 := by
  unfold tailWord_470402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289242610455341777663365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11437980294547578073768973 4289242610455341777663365)
  ·
    refine ⟨804232989460376583311881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4289242610455341777663365 804232989460376583311881)
    ·
      refine ⟨603174742095282437483911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 804232989460376583311881 603174742095282437483911)
      ·
        refine ⟨904762113142923656225867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603174742095282437483911 904762113142923656225867)
        ·
          refine ⟨1357143169714385484338801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904762113142923656225867 1357143169714385484338801)
          ·
            refine ⟨1017857377285789113254101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1357143169714385484338801 1017857377285789113254101)
            ·
              refine ⟨23856032280135682341893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1017857377285789113254101 23856032280135682341893)
              ·
                rfl

theorem cell20_470402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 7].length) (baseStart_470402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470402 prefixEnd_470402 := by exact prefixLift 470402
  have htrace : WordTrace (prefixWord ++ tailWord_470402) baseStart_470402 baseEnd_470402 := by
    simpa [prefixWord, tailWord_470402, baseEnd_470402] using wordTrace_append hprefix tailTrace_470402
  have hstable : (prefixWord ++ tailWord_470402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470402).length < 2 ^ (prefixWord ++ tailWord_470402).sum := by decide
  have hdescent : baseEnd_470402 < baseStart_470402 := by decide
  rcases family_descends (prefixWord ++ tailWord_470402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470440 : List Nat := [2, 1, 6, 1, 2, 1, 1, 6]
def baseStart_470440 : Nat := 118140960795 + 470440 * 2 ^ 59
def prefixEnd_470440 : Nat := 4983230072969 + 3 ^ 40 * 470440 * 2
def baseEnd_470440 : Nat := 71573878252220632603405

theorem tailTrace_470440 : CollatzResearch.WordTrace tailWord_470440 prefixEnd_470440 71573878252220632603405 := by
  unfold tailWord_470440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8579178207841849800268387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11438904277122466400357849 8579178207841849800268387)
  ·
    refine ⟨12868767311762774700402581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8579178207841849800268387 12868767311762774700402581)
    ·
      refine ⟨603223467738880064081371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12868767311762774700402581 603223467738880064081371)
      ·
        refine ⟨904835201608320096122057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603223467738880064081371 904835201608320096122057)
        ·
          refine ⟨678626401206240072091543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904835201608320096122057 678626401206240072091543)
          ·
            refine ⟨1017939601809360108137315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678626401206240072091543 1017939601809360108137315)
            ·
              refine ⟨1526909402714040162205973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017939601809360108137315 1526909402714040162205973)
              ·
                refine ⟨71573878252220632603405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1526909402714040162205973 71573878252220632603405)
                ·
                  rfl

theorem cell20_470440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_470440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470440 prefixEnd_470440 := by exact prefixLift 470440
  have htrace : WordTrace (prefixWord ++ tailWord_470440) baseStart_470440 baseEnd_470440 := by
    simpa [prefixWord, tailWord_470440, baseEnd_470440] using wordTrace_append hprefix tailTrace_470440
  have hstable : (prefixWord ++ tailWord_470440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470440).length < 2 ^ (prefixWord ++ tailWord_470440).sum := by decide
  have hdescent : baseEnd_470440 < baseStart_470440 := by decide
  rcases family_descends (prefixWord ++ tailWord_470440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470471 : List Nat := [1, 1, 4, 1, 1, 3, 5, 2, 2]
def baseStart_470471 : Nat := 118140960795 + 470471 * 2 ^ 59
def prefixEnd_470471 : Nat := 4983230072969 + 3 ^ 40 * 470471 * 2
def baseEnd_470471 : Nat := 214735784001363567776755

theorem tailTrace_470471 : CollatzResearch.WordTrace tailWord_470471 prefixEnd_470471 214735784001363567776755 := by
  unfold tailWord_470471
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159487078571391894915267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11439658052380927929943511 17159487078571391894915267)
  ·
    refine ⟨25739230617857087842372901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17159487078571391894915267 25739230617857087842372901)
    ·
      refine ⟨4826105740848203970444919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25739230617857087842372901 4826105740848203970444919)
      ·
        refine ⟨7239158611272305955667379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826105740848203970444919 7239158611272305955667379)
        ·
          refine ⟨10858737916908458933501069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239158611272305955667379 10858737916908458933501069)
          ·
            refine ⟨4072026718840672100062901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10858737916908458933501069 4072026718840672100062901)
            ·
              refine ⟨381752504891313009380897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4072026718840672100062901 381752504891313009380897)
              ·
                refine ⟨286314378668484757035673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381752504891313009380897 286314378668484757035673)
                ·
                  refine ⟨214735784001363567776755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286314378668484757035673 214735784001363567776755)
                  ·
                    rfl

theorem cell20_470471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 2].length) (baseStart_470471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470471 prefixEnd_470471 := by exact prefixLift 470471
  have htrace : WordTrace (prefixWord ++ tailWord_470471) baseStart_470471 baseEnd_470471 := by
    simpa [prefixWord, tailWord_470471, baseEnd_470471] using wordTrace_append hprefix tailTrace_470471
  have hstable : (prefixWord ++ tailWord_470471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470471).length < 2 ^ (prefixWord ++ tailWord_470471).sum := by decide
  have hdescent : baseEnd_470471 < baseStart_470471 := by decide
  rcases family_descends (prefixWord ++ tailWord_470471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470475 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_470475 : Nat := 118140960795 + 470475 * 2 ^ 59
def prefixEnd_470475 : Nat := 4983230072969 + 3 ^ 40 * 470475 * 2
def baseEnd_470475 : Nat := 214737609710357331643405

theorem tailTrace_470475 : CollatzResearch.WordTrace tailWord_470475 prefixEnd_470475 214737609710357331643405 := by
  unfold tailWord_470475
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159632970556900578060879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11439755313704600385373919 17159632970556900578060879)
  ·
    refine ⟨25739449455835350867091319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17159632970556900578060879 25739449455835350867091319)
    ·
      refine ⟨38609174183753026300636979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25739449455835350867091319 38609174183753026300636979)
      ·
        refine ⟨57913761275629539450955469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38609174183753026300636979 57913761275629539450955469)
        ·
          refine ⟨21717660478361077294108301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57913761275629539450955469 21717660478361077294108301)
          ·
            refine ⟨8144122679385403985290613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21717660478361077294108301 8144122679385403985290613)
            ·
              refine ⟨763511501192381623620995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8144122679385403985290613 763511501192381623620995)
              ·
                refine ⟨1145267251788572435431493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763511501192381623620995 1145267251788572435431493)
                ·
                  refine ⟨214737609710357331643405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145267251788572435431493 214737609710357331643405)
                  ·
                    rfl

theorem cell20_470475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_470475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470475 prefixEnd_470475 := by exact prefixLift 470475
  have htrace : WordTrace (prefixWord ++ tailWord_470475) baseStart_470475 baseEnd_470475 := by
    simpa [prefixWord, tailWord_470475, baseEnd_470475] using wordTrace_append hprefix tailTrace_470475
  have hstable : (prefixWord ++ tailWord_470475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470475).length < 2 ^ (prefixWord ++ tailWord_470475).sum := by decide
  have hdescent : baseEnd_470475 < baseStart_470475 := by decide
  rcases family_descends (prefixWord ++ tailWord_470475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470565 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_470565 : Nat := 118140960795 + 470565 * 2 ^ 59
def prefixEnd_470565 : Nat := 4983230072969 + 3 ^ 40 * 470565 * 2
def baseEnd_470565 : Nat := 214778688162717018643037

theorem tailTrace_470565 : CollatzResearch.WordTrace tailWord_470565 prefixEnd_470565 214778688162717018643037 := by
  unfold tailWord_470565
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162915540230845948837149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11441943693487230632558099 17162915540230845948837149)
  ·
    refine ⟨6436093327586567230813931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17162915540230845948837149 6436093327586567230813931)
    ·
      refine ⟨9654139991379850846220897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436093327586567230813931 9654139991379850846220897)
      ·
        refine ⟨7240604993534888134665673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9654139991379850846220897 7240604993534888134665673)
        ·
          refine ⟨5430453745151166100999255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7240604993534888134665673 5430453745151166100999255)
          ·
            refine ⟨8145680617726749151498883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430453745151166100999255 8145680617726749151498883)
            ·
              refine ⟨12218520926590123727248325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8145680617726749151498883 12218520926590123727248325)
              ·
                refine ⟨2290972673735648198859061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12218520926590123727248325 2290972673735648198859061)
                ·
                  refine ⟨214778688162717018643037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290972673735648198859061 214778688162717018643037)
                  ·
                    rfl

theorem cell20_470565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_470565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470565 prefixEnd_470565 := by exact prefixLift 470565
  have htrace : WordTrace (prefixWord ++ tailWord_470565) baseStart_470565 baseEnd_470565 := by
    simpa [prefixWord, tailWord_470565, baseEnd_470565] using wordTrace_append hprefix tailTrace_470565
  have hstable : (prefixWord ++ tailWord_470565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470565).length < 2 ^ (prefixWord ++ tailWord_470565).sum := by decide
  have hdescent : baseEnd_470565 < baseStart_470565 := by decide
  rcases family_descends (prefixWord ++ tailWord_470565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470620 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_470620 : Nat := 118140960795 + 470620 * 2 ^ 59
def prefixEnd_470620 : Nat := 4983230072969 + 3 ^ 40 * 470620 * 2
def baseEnd_470620 : Nat := 214803791661381271809479

theorem tailTrace_470620 : CollatzResearch.WordTrace tailWord_470620 prefixEnd_470620 214803791661381271809479 := by
  unfold tailWord_470620
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582460777515795171044657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11443281036687726894726209 8582460777515795171044657)
  ·
    refine ⟨6436845583136846378283493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8582460777515795171044657 6436845583136846378283493)
    ·
      refine ⟨1206908546838158695928155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6436845583136846378283493 1206908546838158695928155)
      ·
        refine ⟨1810362820257238043892233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206908546838158695928155 1810362820257238043892233)
        ·
          refine ⟨1357772115192928532919175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1810362820257238043892233 1357772115192928532919175)
          ·
            refine ⟨2036658172789392799378763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357772115192928532919175 2036658172789392799378763)
            ·
              refine ⟨3054987259184089199068145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036658172789392799378763 3054987259184089199068145)
              ·
                refine ⟨2291240444388066899301109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054987259184089199068145 2291240444388066899301109)
                ·
                  refine ⟨214803791661381271809479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291240444388066899301109 214803791661381271809479)
                  ·
                    rfl

theorem cell20_470620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_470620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470620 prefixEnd_470620 := by exact prefixLift 470620
  have htrace : WordTrace (prefixWord ++ tailWord_470620) baseStart_470620 baseEnd_470620 := by
    simpa [prefixWord, tailWord_470620, baseEnd_470620] using wordTrace_append hprefix tailTrace_470620
  have hstable : (prefixWord ++ tailWord_470620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470620).length < 2 ^ (prefixWord ++ tailWord_470620).sum := by decide
  have hdescent : baseEnd_470620 < baseStart_470620 := by decide
  rcases family_descends (prefixWord ++ tailWord_470620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470634 : List Nat := [3, 1, 3, 2, 1, 2, 8]
def baseStart_470634 : Nat := 118140960795 + 470634 * 2 ^ 59
def prefixEnd_470634 : Nat := 4983230072969 + 3 ^ 40 * 470634 * 2
def baseEnd_470634 : Nat := 23867797960317716149195

theorem tailTrace_470634 : CollatzResearch.WordTrace tailWord_470634 prefixEnd_470634 23867797960317716149195 := by
  unfold tailWord_470634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291358044245217683274739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11443621451320580488732637 4291358044245217683274739)
  ·
    refine ⟨6437037066367826524912109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4291358044245217683274739 6437037066367826524912109)
    ·
      refine ⟨2413888899887934946842041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6437037066367826524912109 2413888899887934946842041)
      ·
        refine ⟨1810416674915951210131531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2413888899887934946842041 1810416674915951210131531)
        ·
          refine ⟨2715625012373926815197297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810416674915951210131531 2715625012373926815197297)
          ·
            refine ⟨2036718759280445111397973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715625012373926815197297 2036718759280445111397973)
            ·
              refine ⟨23867797960317716149195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2036718759280445111397973 23867797960317716149195)
              ·
                rfl

theorem cell20_470634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_470634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470634 prefixEnd_470634 := by exact prefixLift 470634
  have htrace : WordTrace (prefixWord ++ tailWord_470634) baseStart_470634 baseEnd_470634 := by
    simpa [prefixWord, tailWord_470634, baseEnd_470634] using wordTrace_append hprefix tailTrace_470634
  have hstable : (prefixWord ++ tailWord_470634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470634).length < 2 ^ (prefixWord ++ tailWord_470634).sum := by decide
  have hdescent : baseEnd_470634 < baseStart_470634 := by decide
  rcases family_descends (prefixWord ++ tailWord_470634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470731 : List Nat := [1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_470731 : Nat := 118140960795 + 470731 * 2 ^ 59
def prefixEnd_470731 : Nat := 4983230072969 + 3 ^ 40 * 470731 * 2
def baseEnd_470731 : Nat := 71618151695319406369675

theorem tailTrace_470731 : CollatzResearch.WordTrace tailWord_470731 prefixEnd_470731 71618151695319406369675 := by
  unfold tailWord_470731
  simp only [CollatzResearch.WordTrace]
  refine ⟨17168970057629456299380047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11445980038419637532920031 17168970057629456299380047)
  ·
    refine ⟨25753455086444184449070071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17168970057629456299380047 25753455086444184449070071)
    ·
      refine ⟨38630182629666276673605107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25753455086444184449070071 38630182629666276673605107)
      ·
        refine ⟨57945273944499415010407661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38630182629666276673605107 57945273944499415010407661)
        ·
          refine ⟨21729477729187280628902873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57945273944499415010407661 21729477729187280628902873)
          ·
            refine ⟨16297108296890460471677155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21729477729187280628902873 16297108296890460471677155)
            ·
              refine ⟨24445662445335690707515733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16297108296890460471677155 24445662445335690707515733)
              ·
                refine ⟨71618151695319406369675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24445662445335690707515733 71618151695319406369675)
                ·
                  rfl

theorem cell20_470731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_470731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470731 prefixEnd_470731 := by exact prefixLift 470731
  have htrace : WordTrace (prefixWord ++ tailWord_470731) baseStart_470731 baseEnd_470731 := by
    simpa [prefixWord, tailWord_470731, baseEnd_470731] using wordTrace_append hprefix tailTrace_470731
  have hstable : (prefixWord ++ tailWord_470731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470731).length < 2 ^ (prefixWord ++ tailWord_470731).sum := by decide
  have hdescent : baseEnd_470731 < baseStart_470731 := by decide
  rcases family_descends (prefixWord ++ tailWord_470731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470796 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 2]
def baseStart_470796 : Nat := 118140960795 + 470796 * 2 ^ 59
def prefixEnd_470796 : Nat := 4983230072969 + 3 ^ 40 * 470796 * 2
def baseEnd_470796 : Nat := 214884122857106881942093

theorem tailTrace_470796 : CollatzResearch.WordTrace tailWord_470796 prefixEnd_470796 214884122857106881942093 := by
  unfold tailWord_470796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585670401196986200248121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11447560534929314933664161 8585670401196986200248121)
  ·
    refine ⟨6439252800897739650186091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8585670401196986200248121 6439252800897739650186091)
    ·
      refine ⟨9658879201346609475279137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439252800897739650186091 9658879201346609475279137)
      ·
        refine ⟨7244159401009957106459353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9658879201346609475279137 7244159401009957106459353)
        ·
          refine ⟨5433119550757467829844515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7244159401009957106459353 5433119550757467829844515)
          ·
            refine ⟨8149679326136201744766773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433119550757467829844515 8149679326136201744766773)
            ·
              refine ⟨764032436825268913571885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8149679326136201744766773 764032436825268913571885)
              ·
                refine ⟨286512163809475842589457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 764032436825268913571885 286512163809475842589457)
                ·
                  refine ⟨214884122857106881942093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286512163809475842589457 214884122857106881942093)
                  ·
                    rfl

theorem cell20_470796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_470796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470796 prefixEnd_470796 := by exact prefixLift 470796
  have htrace : WordTrace (prefixWord ++ tailWord_470796) baseStart_470796 baseEnd_470796 := by
    simpa [prefixWord, tailWord_470796, baseEnd_470796] using wordTrace_append hprefix tailTrace_470796
  have hstable : (prefixWord ++ tailWord_470796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470796).length < 2 ^ (prefixWord ++ tailWord_470796).sum := by decide
  have hdescent : baseEnd_470796 < baseStart_470796 := by decide
  rcases family_descends (prefixWord ++ tailWord_470796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470817 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_470817 : Nat := 118140960795 + 470817 * 2 ^ 59
def prefixEnd_470817 : Nat := 4983230072969 + 3 ^ 40 * 470817 * 2
def baseEnd_470817 : Nat := 214893707829324142242007

theorem tailTrace_470817 : CollatzResearch.WordTrace tailWord_470817 prefixEnd_470817 214893707829324142242007 := by
  unfold tailWord_470817
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172106735317892987010705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11448071156878595324673803 17172106735317892987010705)
  ·
    refine ⟨12879080051488419740258029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17172106735317892987010705 12879080051488419740258029)
    ·
      refine ⟨4829655019308157402596761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12879080051488419740258029 4829655019308157402596761)
      ·
        refine ⟨3622241264481118051947571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4829655019308157402596761 3622241264481118051947571)
        ·
          refine ⟨5433361896721677077921357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622241264481118051947571 5433361896721677077921357)
          ·
            refine ⟨2037510711270628904220509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5433361896721677077921357 2037510711270628904220509)
            ·
              refine ⟨764066516726485839082691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2037510711270628904220509 764066516726485839082691)
              ·
                refine ⟨1146099775089728758624037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764066516726485839082691 1146099775089728758624037)
                ·
                  refine ⟨214893707829324142242007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146099775089728758624037 214893707829324142242007)
                  ·
                    rfl

theorem cell20_470817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_470817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470817 prefixEnd_470817 := by exact prefixLift 470817
  have htrace : WordTrace (prefixWord ++ tailWord_470817) baseStart_470817 baseEnd_470817 := by
    simpa [prefixWord, tailWord_470817, baseEnd_470817] using wordTrace_append hprefix tailTrace_470817
  have hstable : (prefixWord ++ tailWord_470817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470817).length < 2 ^ (prefixWord ++ tailWord_470817).sum := by decide
  have hdescent : baseEnd_470817 < baseStart_470817 := by decide
  rcases family_descends (prefixWord ++ tailWord_470817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470824 : List Nat := [2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_470824 : Nat := 118140960795 + 470824 * 2 ^ 59
def prefixEnd_470824 : Nat := 4983230072969 + 3 ^ 40 * 470824 * 2
def baseEnd_470824 : Nat := 71632300940021076336215

theorem tailTrace_470824 : CollatzResearch.WordTrace tailWord_470824 prefixEnd_470824 71632300940021076336215 := by
  unfold tailWord_470824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586181023146266591257763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11448241364195022121677017 8586181023146266591257763)
  ·
    refine ⟨12879271534719399886886645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8586181023146266591257763 12879271534719399886886645)
    ·
      refine ⟨1207431706379943739395623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12879271534719399886886645 1207431706379943739395623)
      ·
        refine ⟨1811147559569915609093435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207431706379943739395623 1811147559569915609093435)
        ·
          refine ⟨2716721339354873413640153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811147559569915609093435 2716721339354873413640153)
          ·
            refine ⟨2037541004516155060230115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2716721339354873413640153 2037541004516155060230115)
            ·
              refine ⟨3056311506774232590345173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037541004516155060230115 3056311506774232590345173)
              ·
                refine ⟨71632300940021076336215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3056311506774232590345173 71632300940021076336215)
                ·
                  rfl

theorem cell20_470824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_470824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470824 prefixEnd_470824 := by exact prefixLift 470824
  have htrace : WordTrace (prefixWord ++ tailWord_470824) baseStart_470824 baseEnd_470824 := by
    simpa [prefixWord, tailWord_470824, baseEnd_470824] using wordTrace_append hprefix tailTrace_470824
  have hstable : (prefixWord ++ tailWord_470824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470824).length < 2 ^ (prefixWord ++ tailWord_470824).sum := by decide
  have hdescent : baseEnd_470824 < baseStart_470824 := by decide
  rcases family_descends (prefixWord ++ tailWord_470824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470831 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_470831 : Nat := 118140960795 + 470831 * 2 ^ 59
def prefixEnd_470831 : Nat := 4983230072969 + 3 ^ 40 * 470831 * 2
def baseEnd_470831 : Nat := 214900097810802315775283

theorem tailTrace_470831 : CollatzResearch.WordTrace tailWord_470831 prefixEnd_470831 214900097810802315775283 := by
  unfold tailWord_470831
  simp only [CollatzResearch.WordTrace]
  refine ⟨17172617357267173378020347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11448411571511448918680231 17172617357267173378020347)
  ·
    refine ⟨25758926035900760067030521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17172617357267173378020347 25758926035900760067030521)
    ·
      refine ⟨19319194526925570050272891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25758926035900760067030521 19319194526925570050272891)
      ·
        refine ⟨28978791790388355075409337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19319194526925570050272891 28978791790388355075409337)
        ·
          refine ⟨21734093842791266306557003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28978791790388355075409337 21734093842791266306557003)
          ·
            refine ⟨32601140764186899459835505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21734093842791266306557003 32601140764186899459835505)
            ·
              refine ⟨24450855573140174594876629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32601140764186899459835505 24450855573140174594876629)
              ·
                refine ⟨573066927495472842067421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24450855573140174594876629 573066927495472842067421)
                ·
                  refine ⟨214900097810802315775283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573066927495472842067421 214900097810802315775283)
                  ·
                    rfl

theorem cell20_470831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_470831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470831 prefixEnd_470831 := by exact prefixLift 470831
  have htrace : WordTrace (prefixWord ++ tailWord_470831) baseStart_470831 baseEnd_470831 := by
    simpa [prefixWord, tailWord_470831, baseEnd_470831] using wordTrace_append hprefix tailTrace_470831
  have hstable : (prefixWord ++ tailWord_470831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470831).length < 2 ^ (prefixWord ++ tailWord_470831).sum := by decide
  have hdescent : baseEnd_470831 < baseStart_470831 := by decide
  rcases family_descends (prefixWord ++ tailWord_470831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470868 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 2]
def baseStart_470868 : Nat := 118140960795 + 470868 * 2 ^ 59
def prefixEnd_470868 : Nat := 4983230072969 + 3 ^ 40 * 470868 * 2
def baseEnd_470868 : Nat := 214916985618994631541799

theorem tailTrace_470868 : CollatzResearch.WordTrace tailWord_470868 prefixEnd_470868 214916985618994631541799 := by
  unfold tailWord_470868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586983429066564348558629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11449311238755419131411505 8586983429066564348558629)
  ·
    refine ⟨1610059392949980815354743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8586983429066564348558629 1610059392949980815354743)
    ·
      refine ⟨2415089089424971223032115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610059392949980815354743 2415089089424971223032115)
      ·
        refine ⟨3622633634137456834548173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415089089424971223032115 3622633634137456834548173)
        ·
          refine ⟨1358487612801546312955565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3622633634137456834548173 1358487612801546312955565)
          ·
            refine ⟨509432854800579867358337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1358487612801546312955565 509432854800579867358337)
            ·
              refine ⟨382074641100434900518753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509432854800579867358337 382074641100434900518753)
              ·
                refine ⟨286555980825326175389065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382074641100434900518753 286555980825326175389065)
                ·
                  refine ⟨214916985618994631541799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286555980825326175389065 214916985618994631541799)
                  ·
                    rfl

theorem cell20_470868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_470868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470868 prefixEnd_470868 := by exact prefixLift 470868
  have htrace : WordTrace (prefixWord ++ tailWord_470868) baseStart_470868 baseEnd_470868 := by
    simpa [prefixWord, tailWord_470868, baseEnd_470868] using wordTrace_append hprefix tailTrace_470868
  have hstable : (prefixWord ++ tailWord_470868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470868).length < 2 ^ (prefixWord ++ tailWord_470868).sum := by decide
  have hdescent : baseEnd_470868 < baseStart_470868 := by decide
  rcases family_descends (prefixWord ++ tailWord_470868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470920 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 3]
def baseStart_470920 : Nat := 118140960795 + 470920 * 2 ^ 59
def prefixEnd_470920 : Nat := 4983230072969 + 3 ^ 40 * 470920 * 2
def baseEnd_470920 : Nat := 214940719835913561808253

theorem tailTrace_470920 : CollatzResearch.WordTrace tailWord_470920 prefixEnd_470920 214940719835913561808253 := by
  unfold tailWord_470920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587931726972370789005107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11450575635963161052006809 8587931726972370789005107)
  ·
    refine ⟨12881897590458556183507661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8587931726972370789005107 12881897590458556183507661)
    ·
      refine ⟨4830711596421958568815373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12881897590458556183507661 4830711596421958568815373)
      ·
        refine ⟨1811516848658234463305765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4830711596421958568815373 1811516848658234463305765)
        ·
          refine ⟨339659409123418961869831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1811516848658234463305765 339659409123418961869831)
          ·
            refine ⟨509489113685128442804747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339659409123418961869831 509489113685128442804747)
            ·
              refine ⟨764233670527692664207121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509489113685128442804747 764233670527692664207121)
              ·
                refine ⟨573175252895769498155341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764233670527692664207121 573175252895769498155341)
                ·
                  refine ⟨214940719835913561808253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573175252895769498155341 214940719835913561808253)
                  ·
                    rfl

theorem cell20_470920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_470920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470920 prefixEnd_470920 := by exact prefixLift 470920
  have htrace : WordTrace (prefixWord ++ tailWord_470920) baseStart_470920 baseEnd_470920 := by
    simpa [prefixWord, tailWord_470920, baseEnd_470920] using wordTrace_append hprefix tailTrace_470920
  have hstable : (prefixWord ++ tailWord_470920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470920).length < 2 ^ (prefixWord ++ tailWord_470920).sum := by decide
  have hdescent : baseEnd_470920 < baseStart_470920 := by decide
  rcases family_descends (prefixWord ++ tailWord_470920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470921 : List Nat := [1, 2, 1, 1, 5, 1, 9]
def baseStart_470921 : Nat := 118140960795 + 470921 * 2 ^ 59
def prefixEnd_470921 : Nat := 4983230072969 + 3 ^ 40 * 470921 * 2
def baseEnd_470921 : Nat := 23882352918129111419435

theorem tailTrace_470921 : CollatzResearch.WordTrace tailWord_470921 prefixEnd_470921 23882352918129111419435 := by
  unfold tailWord_470921
  simp only [CollatzResearch.WordTrace]
  refine ⟨17175899926941118748796617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11450599951294079165864411 17175899926941118748796617)
  ·
    refine ⟨12881924945205839061597463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17175899926941118748796617 12881924945205839061597463)
    ·
      refine ⟨19322887417808758592396195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12881924945205839061597463 19322887417808758592396195)
      ·
        refine ⟨28984331126713137888594293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19322887417808758592396195 28984331126713137888594293)
        ·
          refine ⟨2717281043129356677055715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28984331126713137888594293 2717281043129356677055715)
          ·
            refine ⟨4075921564694035015583573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717281043129356677055715 4075921564694035015583573)
            ·
              refine ⟨23882352918129111419435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4075921564694035015583573 23882352918129111419435)
              ·
                rfl

theorem cell20_470921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_470921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470921 prefixEnd_470921 := by exact prefixLift 470921
  have htrace : WordTrace (prefixWord ++ tailWord_470921) baseStart_470921 baseEnd_470921 := by
    simpa [prefixWord, tailWord_470921, baseEnd_470921] using wordTrace_append hprefix tailTrace_470921
  have hstable : (prefixWord ++ tailWord_470921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470921).length < 2 ^ (prefixWord ++ tailWord_470921).sum := by decide
  have hdescent : baseEnd_470921 < baseStart_470921 := by decide
  rcases family_descends (prefixWord ++ tailWord_470921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470941 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 3]
def baseStart_470941 : Nat := 118140960795 + 470941 * 2 ^ 59
def prefixEnd_470941 : Nat := 4983230072969 + 3 ^ 40 * 470941 * 2
def baseEnd_470941 : Nat := 214950304808130822108167

theorem tailTrace_470941 : CollatzResearch.WordTrace tailWord_470941 prefixEnd_470941 214950304808130822108167 := by
  unfold tailWord_470941
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176629386868662164524677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11451086257912441443016451 17176629386868662164524677)
  ·
    refine ⟨3220618010037874155848377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17176629386868662164524677 3220618010037874155848377)
    ·
      refine ⟨2415463507528405616886283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220618010037874155848377 2415463507528405616886283)
      ·
        refine ⟨3623195261292608425329425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415463507528405616886283 3623195261292608425329425)
        ·
          refine ⟨2717396445969456318997069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623195261292608425329425 2717396445969456318997069)
          ·
            refine ⟨1019023667238546119623901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2717396445969456318997069 1019023667238546119623901)
            ·
              refine ⟨382133875214454794858963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1019023667238546119623901 382133875214454794858963)
              ·
                refine ⟨573200812821682192288445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382133875214454794858963 573200812821682192288445)
                ·
                  refine ⟨214950304808130822108167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573200812821682192288445 214950304808130822108167)
                  ·
                    rfl

theorem cell20_470941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_470941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470941 prefixEnd_470941 := by exact prefixLift 470941
  have htrace : WordTrace (prefixWord ++ tailWord_470941) baseStart_470941 baseEnd_470941 := by
    simpa [prefixWord, tailWord_470941, baseEnd_470941] using wordTrace_append hprefix tailTrace_470941
  have hstable : (prefixWord ++ tailWord_470941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470941).length < 2 ^ (prefixWord ++ tailWord_470941).sum := by decide
  have hdescent : baseEnd_470941 < baseStart_470941 := by decide
  rcases family_descends (prefixWord ++ tailWord_470941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470959 : List Nat := [1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_470959 : Nat := 118140960795 + 470959 * 2 ^ 59
def prefixEnd_470959 : Nat := 4983230072969 + 3 ^ 40 * 470959 * 2
def baseEnd_470959 : Nat := 71652840166200919836031

theorem tailTrace_470959 : CollatzResearch.WordTrace tailWord_470959 prefixEnd_470959 71652840166200919836031 := by
  unfold tailWord_470959
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177285900803451238679931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11451523933868967492453287 17177285900803451238679931)
  ·
    refine ⟨25765928851205176858019897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17177285900803451238679931 25765928851205176858019897)
    ·
      refine ⟨19324446638403882643514923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25765928851205176858019897 19324446638403882643514923)
      ·
        refine ⟨28986669957605823965272385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19324446638403882643514923 28986669957605823965272385)
        ·
          refine ⟨21740002468204367973954289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28986669957605823965272385 21740002468204367973954289)
          ·
            refine ⟨16305001851153275980465717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21740002468204367973954289 16305001851153275980465717)
            ·
              refine ⟨1528593923545619623168661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16305001851153275980465717 1528593923545619623168661)
              ·
                refine ⟨71652840166200919836031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1528593923545619623168661 71652840166200919836031)
                ·
                  rfl

theorem cell20_470959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_470959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470959 prefixEnd_470959 := by exact prefixLift 470959
  have htrace : WordTrace (prefixWord ++ tailWord_470959) baseStart_470959 baseEnd_470959 := by
    simpa [prefixWord, tailWord_470959, baseEnd_470959] using wordTrace_append hprefix tailTrace_470959
  have hstable : (prefixWord ++ tailWord_470959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470959).length < 2 ^ (prefixWord ++ tailWord_470959).sum := by decide
  have hdescent : baseEnd_470959 < baseStart_470959 := by decide
  rcases family_descends (prefixWord ++ tailWord_470959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470965 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 2]
def baseStart_470965 : Nat := 118140960795 + 470965 * 2 ^ 59
def prefixEnd_470965 : Nat := 4983230072969 + 3 ^ 40 * 470965 * 2
def baseEnd_470965 : Nat := 214961259062093405308069

theorem tailTrace_470965 : CollatzResearch.WordTrace tailWord_470965 prefixEnd_470965 214961259062093405308069 := by
  unfold tailWord_470965
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177504738781714263398349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11451669825854476175598899 17177504738781714263398349)
  ·
    refine ⟨6441564277043142848774381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17177504738781714263398349 6441564277043142848774381)
    ·
      refine ⟨2415586603891178568290393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6441564277043142848774381 2415586603891178568290393)
      ·
        refine ⟨1811689952918383926217795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2415586603891178568290393 1811689952918383926217795)
        ·
          refine ⟨2717534929377575889326693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811689952918383926217795 2717534929377575889326693)
          ·
            refine ⟨509537799258295479248755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2717534929377575889326693 509537799258295479248755)
            ·
              refine ⟨764306698887443218873133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509537799258295479248755 764306698887443218873133)
              ·
                refine ⟨286615012082791207077425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 764306698887443218873133 286615012082791207077425)
                ·
                  refine ⟨214961259062093405308069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286615012082791207077425 214961259062093405308069)
                  ·
                    rfl

theorem cell20_470965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_470965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470965 prefixEnd_470965 := by exact prefixLift 470965
  have htrace : WordTrace (prefixWord ++ tailWord_470965) baseStart_470965 baseEnd_470965 := by
    simpa [prefixWord, tailWord_470965, baseEnd_470965] using wordTrace_append hprefix tailTrace_470965
  have hstable : (prefixWord ++ tailWord_470965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470965).length < 2 ^ (prefixWord ++ tailWord_470965).sum := by decide
  have hdescent : baseEnd_470965 < baseStart_470965 := by decide
  rcases family_descends (prefixWord ++ tailWord_470965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470972 : List Nat := [2, 2, 2, 5, 2, 1, 6]
def baseStart_470972 : Nat := 118140960795 + 470972 * 2 ^ 59
def prefixEnd_470972 : Nat := 4983230072969 + 3 ^ 40 * 470972 * 2
def baseEnd_470972 : Nat := 23884939339203610230523

theorem tailTrace_470972 : CollatzResearch.WordTrace tailWord_470972 prefixEnd_470972 23884939339203610230523 := by
  unfold tailWord_470972
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588880024878177229451585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11451840033170902972602113 8588880024878177229451585)
  ·
    refine ⟨6441660018658632922088689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8588880024878177229451585 6441660018658632922088689)
    ·
      refine ⟨4831245013993974691566517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6441660018658632922088689 4831245013993974691566517)
      ·
        refine ⟨452929220061935127334361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4831245013993974691566517 452929220061935127334361)
        ·
          refine ⟨339696915046451345500771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452929220061935127334361 339696915046451345500771)
          ·
            refine ⟨509545372569677018251157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339696915046451345500771 509545372569677018251157)
            ·
              refine ⟨23884939339203610230523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 509545372569677018251157 23884939339203610230523)
              ·
                rfl

theorem cell20_470972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 6].length) (baseStart_470972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470972 prefixEnd_470972 := by exact prefixLift 470972
  have htrace : WordTrace (prefixWord ++ tailWord_470972) baseStart_470972 baseEnd_470972 := by
    simpa [prefixWord, tailWord_470972, baseEnd_470972] using wordTrace_append hprefix tailTrace_470972
  have hstable : (prefixWord ++ tailWord_470972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470972).length < 2 ^ (prefixWord ++ tailWord_470972).sum := by decide
  have hdescent : baseEnd_470972 < baseStart_470972 := by decide
  rcases family_descends (prefixWord ++ tailWord_470972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470983 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_470983 : Nat := 118140960795 + 470983 * 2 ^ 59
def prefixEnd_470983 : Nat := 4983230072969 + 3 ^ 40 * 470983 * 2
def baseEnd_470983 : Nat := 214969474752565342707995

theorem tailTrace_470983 : CollatzResearch.WordTrace tailWord_470983 prefixEnd_470983 214969474752565342707995 := by
  unfold tailWord_470983
  simp only [CollatzResearch.WordTrace]
  refine ⟨17178161252716503337553603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11452107501811002225035735 17178161252716503337553603)
  ·
    refine ⟨25767241879074755006330405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17178161252716503337553603 25767241879074755006330405)
    ·
      refine ⟨4831357852326516563686951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25767241879074755006330405 4831357852326516563686951)
      ·
        refine ⟨7247036778489774845530427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831357852326516563686951 7247036778489774845530427)
        ·
          refine ⟨10870555167734662268295641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7247036778489774845530427 10870555167734662268295641)
          ·
            refine ⟨8152916375800996701221731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10870555167734662268295641 8152916375800996701221731)
            ·
              refine ⟨12229374563701495051832597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152916375800996701221731 12229374563701495051832597)
              ·
                refine ⟨573251932673507580554653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12229374563701495051832597 573251932673507580554653)
                ·
                  refine ⟨214969474752565342707995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573251932673507580554653 214969474752565342707995)
                  ·
                    rfl

theorem cell20_470983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_470983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_470983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_470983 prefixEnd_470983 := by exact prefixLift 470983
  have htrace : WordTrace (prefixWord ++ tailWord_470983) baseStart_470983 baseEnd_470983 := by
    simpa [prefixWord, tailWord_470983, baseEnd_470983] using wordTrace_append hprefix tailTrace_470983
  have hstable : (prefixWord ++ tailWord_470983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470983).length < 2 ^ (prefixWord ++ tailWord_470983).sum := by decide
  have hdescent : baseEnd_470983 < baseStart_470983 := by decide
  rcases family_descends (prefixWord ++ tailWord_470983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471059 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_471059 : Nat := 118140960795 + 471059 * 2 ^ 59
def prefixEnd_471059 : Nat := 4983230072969 + 3 ^ 40 * 471059 * 2
def baseEnd_471059 : Nat := 215004163223446856174351

theorem tailTrace_471059 : CollatzResearch.WordTrace tailWord_471059 prefixEnd_471059 215004163223446856174351 := by
  unfold tailWord_471059
  simp only [CollatzResearch.WordTrace]
  refine ⟨17180933200441168317320231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11453955466960778878213487 17180933200441168317320231)
  ·
    refine ⟨25771399800661752475980347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17180933200441168317320231 25771399800661752475980347)
    ·
      refine ⟨38657099700992628713970521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25771399800661752475980347 38657099700992628713970521)
      ·
        refine ⟨28992824775744471535477891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38657099700992628713970521 28992824775744471535477891)
        ·
          refine ⟨43489237163616707303216837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28992824775744471535477891 43489237163616707303216837)
          ·
            refine ⟨8154231968178132619353157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43489237163616707303216837 8154231968178132619353157)
            ·
              refine ⟨1528918494033399866128717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8154231968178132619353157 1528918494033399866128717)
              ·
                refine ⟨573344435262524949798269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1528918494033399866128717 573344435262524949798269)
                ·
                  refine ⟨215004163223446856174351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573344435262524949798269 215004163223446856174351)
                  ·
                    rfl

theorem cell20_471059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_471059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471059 prefixEnd_471059 := by exact prefixLift 471059
  have htrace : WordTrace (prefixWord ++ tailWord_471059) baseStart_471059 baseEnd_471059 := by
    simpa [prefixWord, tailWord_471059, baseEnd_471059] using wordTrace_append hprefix tailTrace_471059
  have hstable : (prefixWord ++ tailWord_471059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471059).length < 2 ^ (prefixWord ++ tailWord_471059).sum := by decide
  have hdescent : baseEnd_471059 < baseStart_471059 := by decide
  rcases family_descends (prefixWord ++ tailWord_471059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471066 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_471066 : Nat := 118140960795 + 471066 * 2 ^ 59
def prefixEnd_471066 : Nat := 4983230072969 + 3 ^ 40 * 471066 * 2
def baseEnd_471066 : Nat := 215007358214185942940989

theorem tailTrace_471066 : CollatzResearch.WordTrace tailWord_471066 prefixEnd_471066 215007358214185942940989 := by
  unfold tailWord_471066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295297127853952128206263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11454125674277205675216701 4295297127853952128206263)
  ·
    refine ⟨6442945691780928192309395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295297127853952128206263 6442945691780928192309395)
    ·
      refine ⟨9664418537671392288464093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442945691780928192309395 9664418537671392288464093)
      ·
        refine ⟨3624156951626772108174035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9664418537671392288464093 3624156951626772108174035)
        ·
          refine ⟨5436235427440158162261053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624156951626772108174035 5436235427440158162261053)
          ·
            refine ⟨2038588285290059310847895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5436235427440158162261053 2038588285290059310847895)
            ·
              refine ⟨3057882427935088966271843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038588285290059310847895 3057882427935088966271843)
              ·
                refine ⟨4586823641902633449407765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057882427935088966271843 4586823641902633449407765)
                ·
                  refine ⟨215007358214185942940989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4586823641902633449407765 215007358214185942940989)
                  ·
                    rfl

theorem cell20_471066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_471066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471066 prefixEnd_471066 := by exact prefixLift 471066
  have htrace : WordTrace (prefixWord ++ tailWord_471066) baseStart_471066 baseEnd_471066 := by
    simpa [prefixWord, tailWord_471066, baseEnd_471066] using wordTrace_append hprefix tailTrace_471066
  have hstable : (prefixWord ++ tailWord_471066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471066).length < 2 ^ (prefixWord ++ tailWord_471066).sum := by decide
  have hdescent : baseEnd_471066 < baseStart_471066 := by decide
  rcases family_descends (prefixWord ++ tailWord_471066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471069 : List Nat := [1, 4, 2, 2, 2, 2, 3, 4]
def baseStart_471069 : Nat := 118140960795 + 471069 * 2 ^ 59
def prefixEnd_471069 : Nat := 4983230072969 + 3 ^ 40 * 471069 * 2
def baseEnd_471069 : Nat := 71669575831977088613659

theorem tailTrace_471069 : CollatzResearch.WordTrace tailWord_471069 prefixEnd_471069 71669575831977088613659 := by
  unfold tailWord_471069
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181297930404940025184261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11454198620269960016789507 17181297930404940025184261)
  ·
    refine ⟨3221493361950926254722049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17181297930404940025184261 3221493361950926254722049)
    ·
      refine ⟨2416120021463194691041537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3221493361950926254722049 2416120021463194691041537)
      ·
        refine ⟨1812090016097396018281153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2416120021463194691041537 1812090016097396018281153)
        ·
          refine ⟨1359067512073047013710865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812090016097396018281153 1359067512073047013710865)
          ·
            refine ⟨1019300634054785260283149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359067512073047013710865 1019300634054785260283149)
            ·
              refine ⟨382237737770544472606181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1019300634054785260283149 382237737770544472606181)
              ·
                refine ⟨71669575831977088613659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382237737770544472606181 71669575831977088613659)
                ·
                  rfl

theorem cell20_471069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_471069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471069 prefixEnd_471069 := by exact prefixLift 471069
  have htrace : WordTrace (prefixWord ++ tailWord_471069) baseStart_471069 baseEnd_471069 := by
    simpa [prefixWord, tailWord_471069, baseEnd_471069] using wordTrace_append hprefix tailTrace_471069
  have hstable : (prefixWord ++ tailWord_471069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471069).length < 2 ^ (prefixWord ++ tailWord_471069).sum := by decide
  have hdescent : baseEnd_471069 < baseStart_471069 := by decide
  rcases family_descends (prefixWord ++ tailWord_471069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471104 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_471104 : Nat := 118140960795 + 471104 * 2 ^ 59
def prefixEnd_471104 : Nat := 4983230072969 + 3 ^ 40 * 471104 * 2
def baseEnd_471104 : Nat := 215024702449626699674167

theorem tailTrace_471104 : CollatzResearch.WordTrace tailWord_471104 prefixEnd_471104 215024702449626699674167 := by
  unfold tailWord_471104
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591287242639070501354183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11455049656852094001805577 8591287242639070501354183)
  ·
    refine ⟨12886930863958605752031275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8591287242639070501354183 12886930863958605752031275)
    ·
      refine ⟨19330396295937908628046913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12886930863958605752031275 19330396295937908628046913)
      ·
        refine ⟨14497797221953431471035185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19330396295937908628046913 14497797221953431471035185)
        ·
          refine ⟨10873347916465073603276389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14497797221953431471035185 10873347916465073603276389)
          ·
            refine ⟨2038752734337201300614323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10873347916465073603276389 2038752734337201300614323)
            ·
              refine ⟨3058129101505801950921485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038752734337201300614323 3058129101505801950921485)
              ·
                refine ⟨1146798413064675731595557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3058129101505801950921485 1146798413064675731595557)
                ·
                  refine ⟨215024702449626699674167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146798413064675731595557 215024702449626699674167)
                  ·
                    rfl

theorem cell20_471104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_471104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471104 prefixEnd_471104 := by exact prefixLift 471104
  have htrace : WordTrace (prefixWord ++ tailWord_471104) baseStart_471104 baseEnd_471104 := by
    simpa [prefixWord, tailWord_471104, baseEnd_471104] using wordTrace_append hprefix tailTrace_471104
  have hstable : (prefixWord ++ tailWord_471104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471104).length < 2 ^ (prefixWord ++ tailWord_471104).sum := by decide
  have hdescent : baseEnd_471104 < baseStart_471104 := by decide
  rcases family_descends (prefixWord ++ tailWord_471104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471110 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_471110 : Nat := 118140960795 + 471110 * 2 ^ 59
def prefixEnd_471110 : Nat := 4983230072969 + 3 ^ 40 * 471110 * 2
def baseEnd_471110 : Nat := 215027441013117345474143

theorem tailTrace_471110 : CollatzResearch.WordTrace tailWord_471110 prefixEnd_471110 215027441013117345474143 := by
  unfold tailWord_471110
  simp only [CollatzResearch.WordTrace]
  refine ⟨536962291351762625857087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11455195548837602684951189 536962291351762625857087)
  ·
    refine ⟨805443437027643938785631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536962291351762625857087 805443437027643938785631)
    ·
      refine ⟨1208165155541465908178447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805443437027643938785631 1208165155541465908178447)
      ·
        refine ⟨1812247733312198862267671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208165155541465908178447 1812247733312198862267671)
        ·
          refine ⟨2718371599968298293401507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812247733312198862267671 2718371599968298293401507)
          ·
            refine ⟨4077557399952447440102261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718371599968298293401507 4077557399952447440102261)
            ·
              refine ⟨382271006245541947509587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4077557399952447440102261 382271006245541947509587)
              ·
                refine ⟨573406509368312921264381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382271006245541947509587 573406509368312921264381)
                ·
                  refine ⟨215027441013117345474143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573406509368312921264381 215027441013117345474143)
                  ·
                    rfl

theorem cell20_471110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_471110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471110 prefixEnd_471110 := by exact prefixLift 471110
  have htrace : WordTrace (prefixWord ++ tailWord_471110) baseStart_471110 baseEnd_471110 := by
    simpa [prefixWord, tailWord_471110, baseEnd_471110] using wordTrace_append hprefix tailTrace_471110
  have hstable : (prefixWord ++ tailWord_471110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471110).length < 2 ^ (prefixWord ++ tailWord_471110).sum := by decide
  have hdescent : baseEnd_471110 < baseStart_471110 := by decide
  rcases family_descends (prefixWord ++ tailWord_471110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471111 : List Nat := [1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_471111 : Nat := 118140960795 + 471111 * 2 ^ 59
def prefixEnd_471111 : Nat := 4983230072969 + 3 ^ 40 * 471111 * 2
def baseEnd_471111 : Nat := 71675965813455262146935

theorem tailTrace_471111 : CollatzResearch.WordTrace tailWord_471111 prefixEnd_471111 71675965813455262146935 := by
  unfold tailWord_471111
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182829796252781198213187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11455219864168520798808791 17182829796252781198213187)
  ·
    refine ⟨25774244694379171797319781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17182829796252781198213187 25774244694379171797319781)
    ·
      refine ⟨4832670880196094711997459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25774244694379171797319781 4832670880196094711997459)
      ·
        refine ⟨7249006320294142067996189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832670880196094711997459 7249006320294142067996189)
        ·
          refine ⟨2718377370110303275498571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7249006320294142067996189 2718377370110303275498571)
          ·
            refine ⟨4077566055165454913247857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718377370110303275498571 4077566055165454913247857)
            ·
              refine ⟨3058174541374091184935893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077566055165454913247857 3058174541374091184935893)
              ·
                refine ⟨71675965813455262146935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3058174541374091184935893 71675965813455262146935)
                ·
                  rfl

theorem cell20_471111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_471111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471111 prefixEnd_471111 := by exact prefixLift 471111
  have htrace : WordTrace (prefixWord ++ tailWord_471111) baseStart_471111 baseEnd_471111 := by
    simpa [prefixWord, tailWord_471111, baseEnd_471111] using wordTrace_append hprefix tailTrace_471111
  have hstable : (prefixWord ++ tailWord_471111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471111).length < 2 ^ (prefixWord ++ tailWord_471111).sum := by decide
  have hdescent : baseEnd_471111 < baseStart_471111 := by decide
  rcases family_descends (prefixWord ++ tailWord_471111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471128 : List Nat := [2, 1, 2, 2, 1, 4, 4, 4]
def baseStart_471128 : Nat := 118140960795 + 471128 * 2 ^ 59
def prefixEnd_471128 : Nat := 4983230072969 + 3 ^ 40 * 471128 * 2
def baseEnd_471128 : Nat := 71678552234529760958023

theorem tailTrace_471128 : CollatzResearch.WordTrace tailWord_471128 prefixEnd_471128 71678552234529760958023 := by
  unfold tailWord_471128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8591724918595596550791019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11455633224794128734388025 8591724918595596550791019)
  ·
    refine ⟨12887587377893394826186529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8591724918595596550791019 12887587377893394826186529)
    ·
      refine ⟨9665690533420046119639897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12887587377893394826186529 9665690533420046119639897)
      ·
        refine ⟨7249267900065034589729923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9665690533420046119639897 7249267900065034589729923)
        ·
          refine ⟨10873901850097551884594885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7249267900065034589729923 10873901850097551884594885)
          ·
            refine ⟨2038856596893290978361541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10873901850097551884594885 2038856596893290978361541)
            ·
              refine ⟨382285611917492058442789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2038856596893290978361541 382285611917492058442789)
              ·
                refine ⟨71678552234529760958023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382285611917492058442789 71678552234529760958023)
                ·
                  rfl

theorem cell20_471128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_471128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471128 prefixEnd_471128 := by exact prefixLift 471128
  have htrace : WordTrace (prefixWord ++ tailWord_471128) baseStart_471128 baseEnd_471128 := by
    simpa [prefixWord, tailWord_471128, baseEnd_471128] using wordTrace_append hprefix tailTrace_471128
  have hstable : (prefixWord ++ tailWord_471128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471128).length < 2 ^ (prefixWord ++ tailWord_471128).sum := by decide
  have hdescent : baseEnd_471128 < baseStart_471128 := by decide
  rcases family_descends (prefixWord ++ tailWord_471128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471159 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 4]
def baseStart_471159 : Nat := 118140960795 + 471159 * 2 ^ 59
def prefixEnd_471159 : Nat := 4983230072969 + 3 ^ 40 * 471159 * 2
def baseEnd_471159 : Nat := 215049805948290952840609

theorem tailTrace_471159 : CollatzResearch.WordTrace tailWord_471159 prefixEnd_471159 215049805948290952840609 := by
  unfold tailWord_471159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17184580500078885395960531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11456387000052590263973687 17184580500078885395960531)
  ·
    refine ⟨25776870750118328093940797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17184580500078885395960531 25776870750118328093940797)
    ·
      refine ⟨9666326531294373035227799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25776870750118328093940797 9666326531294373035227799)
      ·
        refine ⟨14499489796941559552841699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9666326531294373035227799 14499489796941559552841699)
        ·
          refine ⟨21749234695412339329262549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14499489796941559552841699 21749234695412339329262549)
          ·
            refine ⟨509747688173726703029591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21749234695412339329262549 509747688173726703029591)
            ·
              refine ⟨764621532260590054544387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509747688173726703029591 764621532260590054544387)
              ·
                refine ⟨1146932298390885081816581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764621532260590054544387 1146932298390885081816581)
                ·
                  refine ⟨215049805948290952840609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146932298390885081816581 215049805948290952840609)
                  ·
                    rfl

theorem cell20_471159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_471159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471159 prefixEnd_471159 := by exact prefixLift 471159
  have htrace : WordTrace (prefixWord ++ tailWord_471159) baseStart_471159 baseEnd_471159 := by
    simpa [prefixWord, tailWord_471159, baseEnd_471159] using wordTrace_append hprefix tailTrace_471159
  have hstable : (prefixWord ++ tailWord_471159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471159).length < 2 ^ (prefixWord ++ tailWord_471159).sum := by decide
  have hdescent : baseEnd_471159 < baseStart_471159 := by decide
  rcases family_descends (prefixWord ++ tailWord_471159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471204 : List Nat := [2, 3, 1, 2, 5, 7]
def baseStart_471204 : Nat := 118140960795 + 471204 * 2 ^ 59
def prefixEnd_471204 : Nat := 4983230072969 + 3 ^ 40 * 471204 * 2
def baseEnd_471204 : Nat := 7965568339795214679275

theorem tailTrace_471204 : CollatzResearch.WordTrace tailWord_471204 prefixEnd_471204 7965568339795214679275 := by
  unfold tailWord_471204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8593110892457929040674333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11457481189943905387565777 8593110892457929040674333)
  ·
    refine ⟨3222416584671723390252875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8593110892457929040674333 3222416584671723390252875)
    ·
      refine ⟨4833624877007585085379313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222416584671723390252875 4833624877007585085379313)
      ·
        refine ⟨3625218657755688814034485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4833624877007585085379313 3625218657755688814034485)
        ·
          refine ⟨339864249164595826315733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3625218657755688814034485 339864249164595826315733)
          ·
            refine ⟨7965568339795214679275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 339864249164595826315733 7965568339795214679275)
            ·
              rfl

theorem cell20_471204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 7].length) (baseStart_471204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471204 prefixEnd_471204 := by exact prefixLift 471204
  have htrace : WordTrace (prefixWord ++ tailWord_471204) baseStart_471204 baseEnd_471204 := by
    simpa [prefixWord, tailWord_471204, baseEnd_471204] using wordTrace_append hprefix tailTrace_471204
  have hstable : (prefixWord ++ tailWord_471204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471204).length < 2 ^ (prefixWord ++ tailWord_471204).sum := by decide
  have hdescent : baseEnd_471204 < baseStart_471204 := by decide
  rcases family_descends (prefixWord ++ tailWord_471204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471207 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_471207 : Nat := 118140960795 + 471207 * 2 ^ 59
def prefixEnd_471207 : Nat := 4983230072969 + 3 ^ 40 * 471207 * 2
def baseEnd_471207 : Nat := 215071714456216119240413

theorem tailTrace_471207 : CollatzResearch.WordTrace tailWord_471207 prefixEnd_471207 215071714456216119240413 := by
  unfold tailWord_471207
  simp only [CollatzResearch.WordTrace]
  refine ⟨17186331203904989593707875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11457554135936659729138583 17186331203904989593707875)
  ·
    refine ⟨25779496805857484390561813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17186331203904989593707875 25779496805857484390561813)
    ·
      refine ⟨1208413912774569580807585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25779496805857484390561813 1208413912774569580807585)
      ·
        refine ⟨906310434580927185605689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208413912774569580807585 906310434580927185605689)
        ·
          refine ⟨679732825935695389204267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906310434580927185605689 679732825935695389204267)
          ·
            refine ⟨1019599238903543083806401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679732825935695389204267 1019599238903543083806401)
            ·
              refine ⟨764699429177657312854801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019599238903543083806401 764699429177657312854801)
              ·
                refine ⟨573524571883242984641101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764699429177657312854801 573524571883242984641101)
                ·
                  refine ⟨215071714456216119240413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573524571883242984641101 215071714456216119240413)
                  ·
                    rfl

theorem cell20_471207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_471207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471207 prefixEnd_471207 := by exact prefixLift 471207
  have htrace : WordTrace (prefixWord ++ tailWord_471207) baseStart_471207 baseEnd_471207 := by
    simpa [prefixWord, tailWord_471207, baseEnd_471207] using wordTrace_append hprefix tailTrace_471207
  have hstable : (prefixWord ++ tailWord_471207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471207).length < 2 ^ (prefixWord ++ tailWord_471207).sum := by decide
  have hdescent : baseEnd_471207 < baseStart_471207 := by decide
  rcases family_descends (prefixWord ++ tailWord_471207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471218 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_471218 : Nat := 118140960795 + 471218 * 2 ^ 59
def prefixEnd_471218 : Nat := 4983230072969 + 3 ^ 40 * 471218 * 2
def baseEnd_471218 : Nat := 215076735155948969873701

theorem tailTrace_471218 : CollatzResearch.WordTrace tailWord_471218 prefixEnd_471218 215076735155948969873701 := by
  unfold tailWord_471218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296683101716284618089577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11457821604576758981572205 4296683101716284618089577)
  ·
    refine ⟨3222512326287213463567183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4296683101716284618089577 3222512326287213463567183)
    ·
      refine ⟨4833768489430820195350775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222512326287213463567183 4833768489430820195350775)
      ·
        refine ⟨7250652734146230293026163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833768489430820195350775 7250652734146230293026163)
        ·
          refine ⟨10875979101219345439539245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7250652734146230293026163 10875979101219345439539245)
          ·
            refine ⟨4078492162957254539827217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10875979101219345439539245 4078492162957254539827217)
            ·
              refine ⟨3058869122217940904870413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4078492162957254539827217 3058869122217940904870413)
              ·
                refine ⟨1147075920831727839326405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3058869122217940904870413 1147075920831727839326405)
                ·
                  refine ⟨215076735155948969873701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1147075920831727839326405 215076735155948969873701)
                  ·
                    rfl

theorem cell20_471218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_471218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471218 prefixEnd_471218 := by exact prefixLift 471218
  have htrace : WordTrace (prefixWord ++ tailWord_471218) baseStart_471218 baseEnd_471218 := by
    simpa [prefixWord, tailWord_471218, baseEnd_471218] using wordTrace_append hprefix tailTrace_471218
  have hstable : (prefixWord ++ tailWord_471218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471218).length < 2 ^ (prefixWord ++ tailWord_471218).sum := by decide
  have hdescent : baseEnd_471218 < baseStart_471218 := by decide
  rcases family_descends (prefixWord ++ tailWord_471218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471242 : List Nat := [3, 1, 2, 1, 3, 1, 5, 4]
def baseStart_471242 : Nat := 118140960795 + 471242 * 2 ^ 59
def prefixEnd_471242 : Nat := 4983230072969 + 3 ^ 40 * 471242 * 2
def baseEnd_471242 : Nat := 71695896469970517691201

theorem tailTrace_471242 : CollatzResearch.WordTrace tailWord_471242 prefixEnd_471242 71695896469970517691201 := by
  unfold tailWord_471242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296901939694547642807995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11458405172518793714154653 4296901939694547642807995)
  ·
    refine ⟨6445352909541821464211993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296901939694547642807995 6445352909541821464211993)
    ·
      refine ⟨4834014682156366098158995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6445352909541821464211993 4834014682156366098158995)
      ·
        refine ⟨7251022023234549147238493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834014682156366098158995 7251022023234549147238493)
        ·
          refine ⟨2719133258712955930214435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7251022023234549147238493 2719133258712955930214435)
          ·
            refine ⟨4078699888069433895321653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719133258712955930214435 4078699888069433895321653)
            ·
              refine ⟨382378114506509427686405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4078699888069433895321653 382378114506509427686405)
              ·
                refine ⟨71695896469970517691201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382378114506509427686405 71695896469970517691201)
                ·
                  rfl

theorem cell20_471242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_471242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471242 prefixEnd_471242 := by exact prefixLift 471242
  have htrace : WordTrace (prefixWord ++ tailWord_471242) baseStart_471242 baseEnd_471242 := by
    simpa [prefixWord, tailWord_471242, baseEnd_471242] using wordTrace_append hprefix tailTrace_471242
  have hstable : (prefixWord ++ tailWord_471242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471242).length < 2 ^ (prefixWord ++ tailWord_471242).sum := by decide
  have hdescent : baseEnd_471242 < baseStart_471242 := by decide
  rcases family_descends (prefixWord ++ tailWord_471242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471308 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_471308 : Nat := 118140960795 + 471308 * 2 ^ 59
def prefixEnd_471308 : Nat := 4983230072969 + 3 ^ 40 * 471308 * 2
def baseEnd_471308 : Nat := 215117813608308656873333

theorem tailTrace_471308 : CollatzResearch.WordTrace tailWord_471308 prefixEnd_471308 215117813608308656873333 := by
  unfold tailWord_471308
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595007488269541921567289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11460009984359389228756385 8595007488269541921567289)
  ·
    refine ⟨6446255616202156441175467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8595007488269541921567289 6446255616202156441175467)
    ·
      refine ⟨9669383424303234661763201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446255616202156441175467 9669383424303234661763201)
      ·
        refine ⟨7252037568227425996322401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9669383424303234661763201 7252037568227425996322401)
        ·
          refine ⟨5439028176170569497241801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7252037568227425996322401 5439028176170569497241801)
          ·
            refine ⟨4079271132127927122931351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5439028176170569497241801 4079271132127927122931351)
            ·
              refine ⟨6118906698191890684397027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079271132127927122931351 6118906698191890684397027)
              ·
                refine ⟨9178360047287836026595541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118906698191890684397027 9178360047287836026595541)
                ·
                  refine ⟨215117813608308656873333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9178360047287836026595541 215117813608308656873333)
                  ·
                    rfl

theorem cell20_471308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_471308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471308 prefixEnd_471308 := by exact prefixLift 471308
  have htrace : WordTrace (prefixWord ++ tailWord_471308) baseStart_471308 baseEnd_471308 := by
    simpa [prefixWord, tailWord_471308, baseEnd_471308] using wordTrace_append hprefix tailTrace_471308
  have hstable : (prefixWord ++ tailWord_471308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471308).length < 2 ^ (prefixWord ++ tailWord_471308).sum := by decide
  have hdescent : baseEnd_471308 < baseStart_471308 := by decide
  rcases family_descends (prefixWord ++ tailWord_471308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471315 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_471315 : Nat := 118140960795 + 471315 * 2 ^ 59
def prefixEnd_471315 : Nat := 4983230072969 + 3 ^ 40 * 471315 * 2
def baseEnd_471315 : Nat := 215121008599047743639971

theorem tailTrace_471315 : CollatzResearch.WordTrace tailWord_471315 prefixEnd_471315 215121008599047743639971 := by
  unfold tailWord_471315
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190270287513724038639399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11460180191675816025759599 17190270287513724038639399)
  ·
    refine ⟨25785405431270586057959099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17190270287513724038639399 25785405431270586057959099)
    ·
      refine ⟨38678108146905879086938649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25785405431270586057959099 38678108146905879086938649)
      ·
        refine ⟨29008581110179409315203987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38678108146905879086938649 29008581110179409315203987)
        ·
          refine ⟨43512871665269113972805981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29008581110179409315203987 43512871665269113972805981)
          ·
            refine ⟨16317326874475917739802243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43512871665269113972805981 16317326874475917739802243)
            ·
              refine ⟨24475990311713876609703365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16317326874475917739802243 24475990311713876609703365)
              ·
                refine ⟨4589248183446351864319381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24475990311713876609703365 4589248183446351864319381)
                ·
                  refine ⟨215121008599047743639971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4589248183446351864319381 215121008599047743639971)
                  ·
                    rfl

theorem cell20_471315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_471315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471315 prefixEnd_471315 := by exact prefixLift 471315
  have htrace : WordTrace (prefixWord ++ tailWord_471315) baseStart_471315 baseEnd_471315 := by
    simpa [prefixWord, tailWord_471315, baseEnd_471315] using wordTrace_append hprefix tailTrace_471315
  have hstable : (prefixWord ++ tailWord_471315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471315).length < 2 ^ (prefixWord ++ tailWord_471315).sum := by decide
  have hdescent : baseEnd_471315 < baseStart_471315 := by decide
  rcases family_descends (prefixWord ++ tailWord_471315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471338 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_471338 : Nat := 118140960795 + 471338 * 2 ^ 59
def prefixEnd_471338 : Nat := 4983230072969 + 3 ^ 40 * 471338 * 2
def baseEnd_471338 : Nat := 215131506425761885873211

theorem tailTrace_471338 : CollatzResearch.WordTrace tailWord_471338 prefixEnd_471338 215131506425761885873211 := by
  unfold tailWord_471338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297777291607599741681667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11460739444286932644484445 4297777291607599741681667)
  ·
    refine ⟨6446665937411399612522501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4297777291607599741681667 6446665937411399612522501)
    ·
      refine ⟨1208749863264637427347969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6446665937411399612522501 1208749863264637427347969)
      ·
        refine ⟨906562397448478070510977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208749863264637427347969 906562397448478070510977)
        ·
          refine ⟨679921798086358552883233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906562397448478070510977 679921798086358552883233)
          ·
            refine ⟨509941348564768914662425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679921798086358552883233 509941348564768914662425)
            ·
              refine ⟨382456011423576685996819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509941348564768914662425 382456011423576685996819)
              ·
                refine ⟨573684017135365028995229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382456011423576685996819 573684017135365028995229)
                ·
                  refine ⟨215131506425761885873211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573684017135365028995229 215131506425761885873211)
                  ·
                    rfl

theorem cell20_471338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_471338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471338 prefixEnd_471338 := by exact prefixLift 471338
  have htrace : WordTrace (prefixWord ++ tailWord_471338) baseStart_471338 baseEnd_471338 := by
    simpa [prefixWord, tailWord_471338, baseEnd_471338] using wordTrace_append hprefix tailTrace_471338
  have hstable : (prefixWord ++ tailWord_471338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471338).length < 2 ^ (prefixWord ++ tailWord_471338).sum := by decide
  have hdescent : baseEnd_471338 < baseStart_471338 := by decide
  rcases family_descends (prefixWord ++ tailWord_471338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471380 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_471380 : Nat := 118140960795 + 471380 * 2 ^ 59
def prefixEnd_471380 : Nat := 4983230072969 + 3 ^ 40 * 471380 * 2
def baseEnd_471380 : Nat := 215150676370196406473039

theorem tailTrace_471380 : CollatzResearch.WordTrace tailWord_471380 prefixEnd_471380 215150676370196406473039 := by
  unfold tailWord_471380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596320516139120069877797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11461760688185493426503729 8596320516139120069877797)
  ·
    refine ⟨1611810096776085013102087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8596320516139120069877797 1611810096776085013102087)
    ·
      refine ⟨2417715145164127519653131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611810096776085013102087 2417715145164127519653131)
      ·
        refine ⟨3626572717746191279479697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417715145164127519653131 3626572717746191279479697)
        ·
          refine ⟨2719929538309643459609773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3626572717746191279479697 2719929538309643459609773)
          ·
            refine ⟨1019973576866116297353665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2719929538309643459609773 1019973576866116297353665)
            ·
              refine ⟨764980182649587223015249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019973576866116297353665 764980182649587223015249)
              ·
                refine ⟨573735136987190417261437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764980182649587223015249 573735136987190417261437)
                ·
                  refine ⟨215150676370196406473039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573735136987190417261437 215150676370196406473039)
                  ·
                    rfl

theorem cell20_471380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_471380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471380 prefixEnd_471380 := by exact prefixLift 471380
  have htrace : WordTrace (prefixWord ++ tailWord_471380) baseStart_471380 baseEnd_471380 := by
    simpa [prefixWord, tailWord_471380, baseEnd_471380] using wordTrace_append hprefix tailTrace_471380
  have hstable : (prefixWord ++ tailWord_471380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471380).length < 2 ^ (prefixWord ++ tailWord_471380).sum := by decide
  have hdescent : baseEnd_471380 < baseStart_471380 := by decide
  rcases family_descends (prefixWord ++ tailWord_471380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471394 : List Nat := [3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_471394 : Nat := 118140960795 + 471394 * 2 ^ 59
def prefixEnd_471394 : Nat := 4983230072969 + 3 ^ 40 * 471394 * 2
def baseEnd_471394 : Nat := 71719022117224860002105

theorem tailTrace_471394 : CollatzResearch.WordTrace tailWord_471394 prefixEnd_471394 71719022117224860002105 := by
  unfold tailWord_471394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298287913556880132691309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11462101102818347020510157 4298287913556880132691309)
  ·
    refine ⟨1611857967583830049759241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4298287913556880132691309 1611857967583830049759241)
    ·
      refine ⟨1208893475687872537319431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1611857967583830049759241 1208893475687872537319431)
      ·
        refine ⟨1813340213531808805979147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208893475687872537319431 1813340213531808805979147)
        ·
          refine ⟨2720010320297713208968721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813340213531808805979147 2720010320297713208968721)
          ·
            refine ⟨2040007740223284906726541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720010320297713208968721 2040007740223284906726541)
            ·
              refine ⟨765002902583731840022453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040007740223284906726541 765002902583731840022453)
              ·
                refine ⟨71719022117224860002105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765002902583731840022453 71719022117224860002105)
                ·
                  rfl

theorem cell20_471394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_471394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471394 prefixEnd_471394 := by exact prefixLift 471394
  have htrace : WordTrace (prefixWord ++ tailWord_471394) baseStart_471394 baseEnd_471394 := by
    simpa [prefixWord, tailWord_471394, baseEnd_471394] using wordTrace_append hprefix tailTrace_471394
  have hstable : (prefixWord ++ tailWord_471394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471394).length < 2 ^ (prefixWord ++ tailWord_471394).sum := by decide
  have hdescent : baseEnd_471394 < baseStart_471394 := by decide
  rcases family_descends (prefixWord ++ tailWord_471394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471408 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_471408 : Nat := 118140960795 + 471408 * 2 ^ 59
def prefixEnd_471408 : Nat := 4983230072969 + 3 ^ 40 * 471408 * 2
def baseEnd_471408 : Nat := 215163456333152753539591

theorem tailTrace_471408 : CollatzResearch.WordTrace tailWord_471408 prefixEnd_471408 215163456333152753539591 := by
  unfold tailWord_471408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596831138088400460887439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11462441517451200614516585 8596831138088400460887439)
  ·
    refine ⟨12895246707132600691331159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8596831138088400460887439 12895246707132600691331159)
    ·
      refine ⟨19342870060698901036996739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12895246707132600691331159 19342870060698901036996739)
      ·
        refine ⟨29014305091048351555495109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19342870060698901036996739 29014305091048351555495109)
        ·
          refine ⟨5440182204571565916655333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29014305091048351555495109 5440182204571565916655333)
          ·
            refine ⟨1020034163357168609372875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5440182204571565916655333 1020034163357168609372875)
            ·
              refine ⟨1530051245035752914059313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020034163357168609372875 1530051245035752914059313)
              ·
                refine ⟨1147538433776814685544485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530051245035752914059313 1147538433776814685544485)
                ·
                  refine ⟨215163456333152753539591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1147538433776814685544485 215163456333152753539591)
                  ·
                    rfl

theorem cell20_471408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_471408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471408 prefixEnd_471408 := by exact prefixLift 471408
  have htrace : WordTrace (prefixWord ++ tailWord_471408) baseStart_471408 baseEnd_471408 := by
    simpa [prefixWord, tailWord_471408, baseEnd_471408] using wordTrace_append hprefix tailTrace_471408
  have hstable : (prefixWord ++ tailWord_471408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471408).length < 2 ^ (prefixWord ++ tailWord_471408).sum := by decide
  have hdescent : baseEnd_471408 < baseStart_471408 := by decide
  rcases family_descends (prefixWord ++ tailWord_471408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471429 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_471429 : Nat := 118140960795 + 471429 * 2 ^ 59
def prefixEnd_471429 : Nat := 4983230072969 + 3 ^ 40 * 471429 * 2
def baseEnd_471429 : Nat := 215173041305370013839505

theorem tailTrace_471429 : CollatzResearch.WordTrace tailWord_471429 prefixEnd_471429 215173041305370013839505 := by
  unfold tailWord_471429
  simp only [CollatzResearch.WordTrace]
  refine ⟨17194428209100721508289341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11462952139400481005526227 17194428209100721508289341)
  ·
    refine ⟨6447910578412770565608503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17194428209100721508289341 6447910578412770565608503)
    ·
      refine ⟨9671865867619155848412755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447910578412770565608503 9671865867619155848412755)
      ·
        refine ⟨14507798801428733772619133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9671865867619155848412755 14507798801428733772619133)
        ·
          refine ⟨5440424550535775164732175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14507798801428733772619133 5440424550535775164732175)
          ·
            refine ⟨8160636825803662747098263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5440424550535775164732175 8160636825803662747098263)
            ·
              refine ⟨12240955238705494120647395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8160636825803662747098263 12240955238705494120647395)
              ·
                refine ⟨18361432858058241180971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240955238705494120647395 18361432858058241180971093)
                ·
                  refine ⟨215173041305370013839505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18361432858058241180971093 215173041305370013839505)
                  ·
                    rfl

theorem cell20_471429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_471429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471429 prefixEnd_471429 := by exact prefixLift 471429
  have htrace : WordTrace (prefixWord ++ tailWord_471429) baseStart_471429 baseEnd_471429 := by
    simpa [prefixWord, tailWord_471429, baseEnd_471429] using wordTrace_append hprefix tailTrace_471429
  have hstable : (prefixWord ++ tailWord_471429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471429).length < 2 ^ (prefixWord ++ tailWord_471429).sum := by decide
  have hdescent : baseEnd_471429 < baseStart_471429 := by decide
  rcases family_descends (prefixWord ++ tailWord_471429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471456 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_471456 : Nat := 118140960795 + 471456 * 2 ^ 59
def prefixEnd_471456 : Nat := 4983230072969 + 3 ^ 40 * 471456 * 2
def baseEnd_471456 : Nat := 215185364841077919939395

theorem tailTrace_471456 : CollatzResearch.WordTrace tailWord_471456 prefixEnd_471456 215185364841077919939395 := by
  unfold tailWord_471456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8597706490001452559761111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11463608653335270079681481 8597706490001452559761111)
  ·
    refine ⟨12896559735002178839641667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8597706490001452559761111 12896559735002178839641667)
    ·
      refine ⟨19344839602503268259462501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12896559735002178839641667 19344839602503268259462501)
      ·
        refine ⟨3627157425469362798649219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19344839602503268259462501 3627157425469362798649219)
        ·
          refine ⟨5440736138204044197973829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627157425469362798649219 5440736138204044197973829)
          ·
            refine ⟨1020138025913258287120093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5440736138204044197973829 1020138025913258287120093)
            ·
              refine ⟨382551759717471857670035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1020138025913258287120093 382551759717471857670035)
              ·
                refine ⟨573827639576207786505053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382551759717471857670035 573827639576207786505053)
                ·
                  refine ⟨215185364841077919939395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573827639576207786505053 215185364841077919939395)
                  ·
                    rfl

theorem cell20_471456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_471456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471456 prefixEnd_471456 := by exact prefixLift 471456
  have htrace : WordTrace (prefixWord ++ tailWord_471456) baseStart_471456 baseEnd_471456 := by
    simpa [prefixWord, tailWord_471456, baseEnd_471456] using wordTrace_append hprefix tailTrace_471456
  have hstable : (prefixWord ++ tailWord_471456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471456).length < 2 ^ (prefixWord ++ tailWord_471456).sum := by decide
  have hdescent : baseEnd_471456 < baseStart_471456 := by decide
  rcases family_descends (prefixWord ++ tailWord_471456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471466 : List Nat := [3, 1, 6, 1, 1, 1, 1, 6]
def baseStart_471466 : Nat := 118140960795 + 471466 * 2 ^ 59
def prefixEnd_471466 : Nat := 4983230072969 + 3 ^ 40 * 471466 * 2
def baseEnd_471466 : Nat := 71729976371187443202007

theorem tailTrace_471466 : CollatzResearch.WordTrace tailWord_471466 prefixEnd_471466 71729976371187443202007 := by
  unfold tailWord_471466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298944427491669206846563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11463851806644451218257501 4298944427491669206846563)
  ·
    refine ⟨6448416641237503810269845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4298944427491669206846563 6448416641237503810269845)
    ·
      refine ⟨302269530058007991106399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6448416641237503810269845 302269530058007991106399)
      ·
        refine ⟨453404295087011986659599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302269530058007991106399 453404295087011986659599)
        ·
          refine ⟨680106442630517979989399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453404295087011986659599 680106442630517979989399)
          ·
            refine ⟨1020159663945776969984099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680106442630517979989399 1020159663945776969984099)
            ·
              refine ⟨1530239495918665454976149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020159663945776969984099 1530239495918665454976149)
              ·
                refine ⟨71729976371187443202007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1530239495918665454976149 71729976371187443202007)
                ·
                  rfl

theorem cell20_471466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_471466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471466 prefixEnd_471466 := by exact prefixLift 471466
  have htrace : WordTrace (prefixWord ++ tailWord_471466) baseStart_471466 baseEnd_471466 := by
    simpa [prefixWord, tailWord_471466, baseEnd_471466] using wordTrace_append hprefix tailTrace_471466
  have hstable : (prefixWord ++ tailWord_471466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471466).length < 2 ^ (prefixWord ++ tailWord_471466).sum := by decide
  have hdescent : baseEnd_471466 < baseStart_471466 := by decide
  rcases family_descends (prefixWord ++ tailWord_471466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471498 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_471498 : Nat := 118140960795 + 471498 * 2 ^ 59
def prefixEnd_471498 : Nat := 4983230072969 + 3 ^ 40 * 471498 * 2
def baseEnd_471498 : Nat := 215204534785512440539223

theorem tailTrace_471498 : CollatzResearch.WordTrace tailWord_471498 prefixEnd_471498 215204534785512440539223 := by
  unfold tailWord_471498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299236211462686573137787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11464629897233830861700765 4299236211462686573137787)
  ·
    refine ⟨6448854317194029859706681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299236211462686573137787 6448854317194029859706681)
    ·
      refine ⟨4836640737895522394780011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6448854317194029859706681 4836640737895522394780011)
      ·
        refine ⟨7254961106843283592170017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836640737895522394780011 7254961106843283592170017)
        ·
          refine ⟨5441220830132462694127513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7254961106843283592170017 5441220830132462694127513)
          ·
            refine ⟨4080915622599347020595635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5441220830132462694127513 4080915622599347020595635)
            ·
              refine ⟨6121373433899020530893453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080915622599347020595635 6121373433899020530893453)
              ·
                refine ⟨2295515037712132699085045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6121373433899020530893453 2295515037712132699085045)
                ·
                  refine ⟨215204534785512440539223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2295515037712132699085045 215204534785512440539223)
                  ·
                    rfl

theorem cell20_471498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_471498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471498 prefixEnd_471498 := by exact prefixLift 471498
  have htrace : WordTrace (prefixWord ++ tailWord_471498) baseStart_471498 baseEnd_471498 := by
    simpa [prefixWord, tailWord_471498, baseEnd_471498] using wordTrace_append hprefix tailTrace_471498
  have hstable : (prefixWord ++ tailWord_471498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471498).length < 2 ^ (prefixWord ++ tailWord_471498).sum := by decide
  have hdescent : baseEnd_471498 < baseStart_471498 := by decide
  rcases family_descends (prefixWord ++ tailWord_471498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471508 : List Nat := [2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_471508 : Nat := 118140960795 + 471508 * 2 ^ 59
def prefixEnd_471508 : Nat := 4983230072969 + 3 ^ 40 * 471508 * 2
def baseEnd_471508 : Nat := 71736366352665616735283

theorem tailTrace_471508 : CollatzResearch.WordTrace tailWord_471508 prefixEnd_471508 71736366352665616735283 := by
  unfold tailWord_471508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8598654787907259000207589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11464873050543012000276785 8598654787907259000207589)
  ·
    refine ⟨1612247772732611062538923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8598654787907259000207589 1612247772732611062538923)
    ·
      refine ⟨2418371659098916593808385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612247772732611062538923 2418371659098916593808385)
      ·
        refine ⟨1813778744324187445356289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2418371659098916593808385 1813778744324187445356289)
        ·
          refine ⟨1360334058243140584017217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1813778744324187445356289 1360334058243140584017217)
          ·
            refine ⟨1020250543682355438012913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360334058243140584017217 1020250543682355438012913)
            ·
              refine ⟨765187907761766578509685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020250543682355438012913 765187907761766578509685)
              ·
                refine ⟨71736366352665616735283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765187907761766578509685 71736366352665616735283)
                ·
                  rfl

theorem cell20_471508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_471508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471508 prefixEnd_471508 := by exact prefixLift 471508
  have htrace : WordTrace (prefixWord ++ tailWord_471508) baseStart_471508 baseEnd_471508 := by
    simpa [prefixWord, tailWord_471508, baseEnd_471508] using wordTrace_append hprefix tailTrace_471508
  have hstable : (prefixWord ++ tailWord_471508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471508).length < 2 ^ (prefixWord ++ tailWord_471508).sum := by decide
  have hdescent : baseEnd_471508 < baseStart_471508 := by decide
  rcases family_descends (prefixWord ++ tailWord_471508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471553 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_471553 : Nat := 118140960795 + 471553 * 2 ^ 59
def prefixEnd_471553 : Nat := 4983230072969 + 3 ^ 40 * 471553 * 2
def baseEnd_471553 : Nat := 215229638284176693705665

theorem tailTrace_471553 : CollatzResearch.WordTrace tailWord_471553 prefixEnd_471553 215229638284176693705665 := by
  unfold tailWord_471553
  simp only [CollatzResearch.WordTrace]
  refine ⟨17198950860651490685803313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11465967240434327123868875 17198950860651490685803313)
  ·
    refine ⟨12899213145488618014352485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17198950860651490685803313 12899213145488618014352485)
    ·
      refine ⟨2418602464779115877691091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12899213145488618014352485 2418602464779115877691091)
      ·
        refine ⟨3627903697168673816536637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418602464779115877691091 3627903697168673816536637)
        ·
          refine ⟨1360463886438252681201239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3627903697168673816536637 1360463886438252681201239)
          ·
            refine ⟨2040695829657379021801859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360463886438252681201239 2040695829657379021801859)
            ·
              refine ⟨3061043744486068532702789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040695829657379021801859 3061043744486068532702789)
              ·
                refine ⟨573945702091137849881773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3061043744486068532702789 573945702091137849881773)
                ·
                  refine ⟨215229638284176693705665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573945702091137849881773 215229638284176693705665)
                  ·
                    rfl

theorem cell20_471553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_471553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471553 prefixEnd_471553 := by exact prefixLift 471553
  have htrace : WordTrace (prefixWord ++ tailWord_471553) baseStart_471553 baseEnd_471553 := by
    simpa [prefixWord, tailWord_471553, baseEnd_471553] using wordTrace_append hprefix tailTrace_471553
  have hstable : (prefixWord ++ tailWord_471553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471553).length < 2 ^ (prefixWord ++ tailWord_471553).sum := by decide
  have hdescent : baseEnd_471553 < baseStart_471553 := by decide
  rcases family_descends (prefixWord ++ tailWord_471553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471556 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 2]
def baseStart_471556 : Nat := 118140960795 + 471556 * 2 ^ 59
def prefixEnd_471556 : Nat := 4983230072969 + 3 ^ 40 * 471556 * 2
def baseEnd_471556 : Nat := 215231007565922016605653

theorem tailTrace_471556 : CollatzResearch.WordTrace tailWord_471556 prefixEnd_471556 215231007565922016605653 := by
  unfold tailWord_471556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599530139820311099081261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11466040186427081465441681 8599530139820311099081261)
  ·
    refine ⟨3224823802432616662155473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8599530139820311099081261 3224823802432616662155473)
    ·
      refine ⟨2418617851824462496616605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3224823802432616662155473 2418617851824462496616605)
      ·
        refine ⟨906981694434173436231227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2418617851824462496616605 906981694434173436231227)
        ·
          refine ⟨1360472541651260154346841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906981694434173436231227 1360472541651260154346841)
          ·
            refine ⟨1020354406238445115760131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360472541651260154346841 1020354406238445115760131)
            ·
              refine ⟨1530531609357667673640197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020354406238445115760131 1530531609357667673640197)
              ·
                refine ⟨286974676754562688807537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1530531609357667673640197 286974676754562688807537)
                ·
                  refine ⟨215231007565922016605653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286974676754562688807537 215231007565922016605653)
                  ·
                    rfl

theorem cell20_471556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_471556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471556 prefixEnd_471556 := by exact prefixLift 471556
  have htrace : WordTrace (prefixWord ++ tailWord_471556) baseStart_471556 baseEnd_471556 := by
    simpa [prefixWord, tailWord_471556, baseEnd_471556] using wordTrace_append hprefix tailTrace_471556
  have hstable : (prefixWord ++ tailWord_471556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471556).length < 2 ^ (prefixWord ++ tailWord_471556).sum := by decide
  have hdescent : baseEnd_471556 < baseStart_471556 := by decide
  rcases family_descends (prefixWord ++ tailWord_471556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471594 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_471594 : Nat := 118140960795 + 471594 * 2 ^ 59
def prefixEnd_471594 : Nat := 4983230072969 + 3 ^ 40 * 471594 * 2
def baseEnd_471594 : Nat := 215248351801362773338831

theorem tailTrace_471594 : CollatzResearch.WordTrace tailWord_471594 prefixEnd_471594 215248351801362773338831 := by
  unfold tailWord_471594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300111563375738672011459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11466964169001969792030557 4300111563375738672011459)
  ·
    refine ⟨6450167345063608008017189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4300111563375738672011459 6450167345063608008017189)
    ·
      refine ⟨1209406377199426501503223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6450167345063608008017189 1209406377199426501503223)
      ·
        refine ⟨1814109565799139752254835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209406377199426501503223 1814109565799139752254835)
        ·
          refine ⟨2721164348698709628382253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814109565799139752254835 2721164348698709628382253)
          ·
            refine ⟨1020436630762016110643345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2721164348698709628382253 1020436630762016110643345)
            ·
              refine ⟨765327473071512082982509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020436630762016110643345 765327473071512082982509)
              ·
                refine ⟨286997802401817031118441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765327473071512082982509 286997802401817031118441)
                ·
                  refine ⟨215248351801362773338831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286997802401817031118441 215248351801362773338831)
                  ·
                    rfl

theorem cell20_471594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_471594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471594 prefixEnd_471594 := by exact prefixLift 471594
  have htrace : WordTrace (prefixWord ++ tailWord_471594) baseStart_471594 baseEnd_471594 := by
    simpa [prefixWord, tailWord_471594, baseEnd_471594] using wordTrace_append hprefix tailTrace_471594
  have hstable : (prefixWord ++ tailWord_471594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471594).length < 2 ^ (prefixWord ++ tailWord_471594).sum := by decide
  have hdescent : baseEnd_471594 < baseStart_471594 := by decide
  rcases family_descends (prefixWord ++ tailWord_471594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471604 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_471604 : Nat := 118140960795 + 471604 * 2 ^ 59
def prefixEnd_471604 : Nat := 4983230072969 + 3 ^ 40 * 471604 * 2
def baseEnd_471604 : Nat := 215252916073847183005457

theorem tailTrace_471604 : CollatzResearch.WordTrace tailWord_471604 prefixEnd_471604 215252916073847183005457 := by
  unfold tailWord_471604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600405491733363197954933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11467207322311150930606577 8600405491733363197954933)
  ·
    refine ⟨806288014850002799808275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8600405491733363197954933 806288014850002799808275)
    ·
      refine ⟨1209432022275004199712413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806288014850002799808275 1209432022275004199712413)
      ·
        refine ⟨453537008353126574892155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1209432022275004199712413 453537008353126574892155)
        ·
          refine ⟨680305512529689862338233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453537008353126574892155 680305512529689862338233)
          ·
            refine ⟨510229134397267396753675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680305512529689862338233 510229134397267396753675)
            ·
              refine ⟨765343701595901095130513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510229134397267396753675 765343701595901095130513)
              ·
                refine ⟨574007776196925821347885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765343701595901095130513 574007776196925821347885)
                ·
                  refine ⟨215252916073847183005457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574007776196925821347885 215252916073847183005457)
                  ·
                    rfl

theorem cell20_471604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_471604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471604 prefixEnd_471604 := by exact prefixLift 471604
  have htrace : WordTrace (prefixWord ++ tailWord_471604) baseStart_471604 baseEnd_471604 := by
    simpa [prefixWord, tailWord_471604, baseEnd_471604] using wordTrace_append hprefix tailTrace_471604
  have hstable : (prefixWord ++ tailWord_471604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471604).length < 2 ^ (prefixWord ++ tailWord_471604).sum := by decide
  have hdescent : baseEnd_471604 < baseStart_471604 := by decide
  rcases family_descends (prefixWord ++ tailWord_471604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471636 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_471636 : Nat := 118140960795 + 471636 * 2 ^ 59
def prefixEnd_471636 : Nat := 4983230072969 + 3 ^ 40 * 471636 * 2
def baseEnd_471636 : Nat := 215267521745797293938659

theorem tailTrace_471636 : CollatzResearch.WordTrace tailWord_471636 prefixEnd_471636 215267521745797293938659 := by
  unfold tailWord_471636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600989059675397930537381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11467985412900530574049841 8600989059675397930537381)
  ·
    refine ⟨1612685448689137111975759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8600989059675397930537381 1612685448689137111975759)
    ·
      refine ⟨2419028173033705667963639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612685448689137111975759 2419028173033705667963639)
      ·
        refine ⟨3628542259550558501945459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419028173033705667963639 3628542259550558501945459)
        ·
          refine ⟨5442813389325837752918189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628542259550558501945459 5442813389325837752918189)
          ·
            refine ⟨2041055020997189157344321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5442813389325837752918189 2041055020997189157344321)
            ·
              refine ⟨1530791265747891868008241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041055020997189157344321 1530791265747891868008241)
              ·
                refine ⟨1148093449310918901006181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530791265747891868008241 1148093449310918901006181)
                ·
                  refine ⟨215267521745797293938659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1148093449310918901006181 215267521745797293938659)
                  ·
                    rfl

theorem cell20_471636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_471636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471636 prefixEnd_471636 := by exact prefixLift 471636
  have htrace : WordTrace (prefixWord ++ tailWord_471636) baseStart_471636 baseEnd_471636 := by
    simpa [prefixWord, tailWord_471636, baseEnd_471636] using wordTrace_append hprefix tailTrace_471636
  have hstable : (prefixWord ++ tailWord_471636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471636).length < 2 ^ (prefixWord ++ tailWord_471636).sum := by decide
  have hdescent : baseEnd_471636 < baseStart_471636 := by decide
  rcases family_descends (prefixWord ++ tailWord_471636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471670 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_471670 : Nat := 118140960795 + 471670 * 2 ^ 59
def prefixEnd_471670 : Nat := 4983230072969 + 3 ^ 40 * 471670 * 2
def baseEnd_471670 : Nat := 215283040272244286805187

theorem tailTrace_471670 : CollatzResearch.WordTrace tailWord_471670 prefixEnd_471670 215283040272244286805187 := by
  unfold tailWord_471670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075201137576726229238279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11468812134151746445208309 1075201137576726229238279)
  ·
    refine ⟨1612801706365089343857419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1075201137576726229238279 1612801706365089343857419)
    ·
      refine ⟨2419202559547634015786129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612801706365089343857419 2419202559547634015786129)
      ·
        refine ⟨1814401919660725511839597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2419202559547634015786129 1814401919660725511839597)
        ·
          refine ⟨680400719872772066939849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1814401919660725511839597 680400719872772066939849)
          ·
            refine ⟨510300539904579050204887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680400719872772066939849 510300539904579050204887)
            ·
              refine ⟨765450809856868575307331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510300539904579050204887 765450809856868575307331)
              ·
                refine ⟨1148176214785302862960997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765450809856868575307331 1148176214785302862960997)
                ·
                  refine ⟨215283040272244286805187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1148176214785302862960997 215283040272244286805187)
                  ·
                    rfl

theorem cell20_471670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_471670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471670 prefixEnd_471670 := by exact prefixLift 471670
  have htrace : WordTrace (prefixWord ++ tailWord_471670) baseStart_471670 baseEnd_471670 := by
    simpa [prefixWord, tailWord_471670, baseEnd_471670] using wordTrace_append hprefix tailTrace_471670
  have hstable : (prefixWord ++ tailWord_471670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471670).length < 2 ^ (prefixWord ++ tailWord_471670).sum := by decide
  have hdescent : baseEnd_471670 < baseStart_471670 := by decide
  rcases family_descends (prefixWord ++ tailWord_471670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471681 : List Nat := [1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_471681 : Nat := 118140960795 + 471681 * 2 ^ 59
def prefixEnd_471681 : Nat := 4983230072969 + 3 ^ 40 * 471681 * 2
def baseEnd_471681 : Nat := 71762686990659045812825

theorem tailTrace_471681 : CollatzResearch.WordTrace tailWord_471681 prefixEnd_471681 71762686990659045812825 := by
  unfold tailWord_471681
  simp only [CollatzResearch.WordTrace]
  refine ⟨17203619404187768546462897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11469079602791845697641931 17203619404187768546462897)
  ·
    refine ⟨12902714553140826409847173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17203619404187768546462897 12902714553140826409847173)
    ·
      refine ⟨2419258978713904951846345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12902714553140826409847173 2419258978713904951846345)
      ·
        refine ⟨1814444234035428713884759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2419258978713904951846345 1814444234035428713884759)
        ·
          refine ⟨2721666351053143070827139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814444234035428713884759 2721666351053143070827139)
          ·
            refine ⟨4082499526579714606240709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721666351053143070827139 4082499526579714606240709)
            ·
              refine ⟨765468661233696488670133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4082499526579714606240709 765468661233696488670133)
              ·
                refine ⟨71762686990659045812825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765468661233696488670133 71762686990659045812825)
                ·
                  rfl

theorem cell20_471681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_471681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471681 prefixEnd_471681 := by exact prefixLift 471681
  have htrace : WordTrace (prefixWord ++ tailWord_471681) baseStart_471681 baseEnd_471681 := by
    simpa [prefixWord, tailWord_471681, baseEnd_471681] using wordTrace_append hprefix tailTrace_471681
  have hstable : (prefixWord ++ tailWord_471681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471681).length < 2 ^ (prefixWord ++ tailWord_471681).sum := by decide
  have hdescent : baseEnd_471681 < baseStart_471681 := by decide
  rcases family_descends (prefixWord ++ tailWord_471681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471684 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_471684 : Nat := 118140960795 + 471684 * 2 ^ 59
def prefixEnd_471684 : Nat := 4983230072969 + 3 ^ 40 * 471684 * 2
def baseEnd_471684 : Nat := 215289430253722460338463

theorem tailTrace_471684 : CollatzResearch.WordTrace tailWord_471684 prefixEnd_471684 215289430253722460338463 := by
  unfold tailWord_471684
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601864411588450029411053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11469152548784600039214737 8601864411588450029411053)
  ·
    refine ⟨3225699154345668761029145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8601864411588450029411053 3225699154345668761029145)
    ·
      refine ⟨2419274365759251570771859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3225699154345668761029145 2419274365759251570771859)
      ·
        refine ⟨3628911548638877356157789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419274365759251570771859 3628911548638877356157789)
        ·
          refine ⟨1360841830739579008559171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3628911548638877356157789 1360841830739579008559171)
          ·
            refine ⟨2041262746109368512838757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360841830739579008559171 2041262746109368512838757)
            ·
              refine ⟨382736764895506596157267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2041262746109368512838757 382736764895506596157267)
              ·
                refine ⟨574105147343259894235901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382736764895506596157267 574105147343259894235901)
                ·
                  refine ⟨215289430253722460338463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574105147343259894235901 215289430253722460338463)
                  ·
                    rfl

theorem cell20_471684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_471684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471684 prefixEnd_471684 := by exact prefixLift 471684
  have htrace : WordTrace (prefixWord ++ tailWord_471684) baseStart_471684 baseEnd_471684 := by
    simpa [prefixWord, tailWord_471684, baseEnd_471684] using wordTrace_append hprefix tailTrace_471684
  have hstable : (prefixWord ++ tailWord_471684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471684).length < 2 ^ (prefixWord ++ tailWord_471684).sum := by decide
  have hdescent : baseEnd_471684 < baseStart_471684 := by decide
  rcases family_descends (prefixWord ++ tailWord_471684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471719 : List Nat := [1, 1, 6, 3, 9]
def baseStart_471719 : Nat := 118140960795 + 471719 * 2 ^ 59
def prefixEnd_471719 : Nat := 4983230072969 + 3 ^ 40 * 471719 * 2
def baseEnd_471719 : Nat := 2658091422313801162613

theorem tailTrace_471719 : CollatzResearch.WordTrace tailWord_471719 prefixEnd_471719 2658091422313801162613 := by
  unfold tailWord_471719
  simp only [CollatzResearch.WordTrace]
  refine ⟨17205005378050101036346211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11470003585366734024230807 17205005378050101036346211)
  ·
    refine ⟨25807508067075151554519317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17205005378050101036346211 25807508067075151554519317)
    ·
      refine ⟨1209726940644147729118093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25807508067075151554519317 1209726940644147729118093)
      ·
        refine ⟨453647602741555398419285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1209726940644147729118093 453647602741555398419285)
        ·
          refine ⟨2658091422313801162613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 453647602741555398419285 2658091422313801162613)
          ·
            rfl

theorem cell20_471719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 9].length) (baseStart_471719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471719 prefixEnd_471719 := by exact prefixLift 471719
  have htrace : WordTrace (prefixWord ++ tailWord_471719) baseStart_471719 baseEnd_471719 := by
    simpa [prefixWord, tailWord_471719, baseEnd_471719] using wordTrace_append hprefix tailTrace_471719
  have hstable : (prefixWord ++ tailWord_471719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471719).length < 2 ^ (prefixWord ++ tailWord_471719).sum := by decide
  have hdescent : baseEnd_471719 < baseStart_471719 := by decide
  rcases family_descends (prefixWord ++ tailWord_471719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471725 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 2]
def baseStart_471725 : Nat := 118140960795 + 471725 * 2 ^ 59
def prefixEnd_471725 : Nat := 4983230072969 + 3 ^ 40 * 471725 * 2
def baseEnd_471725 : Nat := 215308143770908539971629

theorem tailTrace_471725 : CollatzResearch.WordTrace tailWord_471725 prefixEnd_471725 215308143770908539971629 := by
  unfold tailWord_471725
  simp only [CollatzResearch.WordTrace]
  refine ⟨17205224216028364061064629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11470149477352242707376419 17205224216028364061064629)
  ·
    refine ⟨1612989770252659130724809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17205224216028364061064629 1612989770252659130724809)
    ·
      refine ⟨1209742327689494348043607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612989770252659130724809 1209742327689494348043607)
      ·
        refine ⟨1814613491534241522065411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209742327689494348043607 1814613491534241522065411)
        ·
          refine ⟨2721920237301362283098117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814613491534241522065411 2721920237301362283098117)
          ·
            refine ⟨510360044494005428080897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2721920237301362283098117 510360044494005428080897)
            ·
              refine ⟨382770033370504071060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510360044494005428080897 382770033370504071060673)
              ·
                refine ⟨287077525027878053295505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382770033370504071060673 287077525027878053295505)
                ·
                  refine ⟨215308143770908539971629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287077525027878053295505 215308143770908539971629)
                  ·
                    rfl

theorem cell20_471725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_471725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471725 prefixEnd_471725 := by exact prefixLift 471725
  have htrace : WordTrace (prefixWord ++ tailWord_471725) baseStart_471725 baseEnd_471725 := by
    simpa [prefixWord, tailWord_471725, baseEnd_471725] using wordTrace_append hprefix tailTrace_471725
  have hstable : (prefixWord ++ tailWord_471725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471725).length < 2 ^ (prefixWord ++ tailWord_471725).sum := by decide
  have hdescent : baseEnd_471725 < baseStart_471725 := by decide
  rcases family_descends (prefixWord ++ tailWord_471725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471767 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 2]
def baseStart_471767 : Nat := 118140960795 + 471767 * 2 ^ 59
def prefixEnd_471767 : Nat := 4983230072969 + 3 ^ 40 * 471767 * 2
def baseEnd_471767 : Nat := 215327313715343060571457

theorem tailTrace_471767 : CollatzResearch.WordTrace tailWord_471767 prefixEnd_471767 215327313715343060571457 := by
  unfold tailWord_471767
  simp only [CollatzResearch.WordTrace]
  refine ⟨17206756081876205234093555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11471170721250803489395703 17206756081876205234093555)
  ·
    refine ⟨25810134122814307851140333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17206756081876205234093555 25810134122814307851140333)
    ·
      refine ⟨9678800296055365444177625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25810134122814307851140333 9678800296055365444177625)
      ·
        refine ⟨7259100222041524083133219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9678800296055365444177625 7259100222041524083133219)
        ·
          refine ⟨10888650333062286124699829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259100222041524083133219 10888650333062286124699829)
          ·
            refine ⟨1020810968724589324190609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10888650333062286124699829 1020810968724589324190609)
            ·
              refine ⟨765608226543441993142957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020810968724589324190609 765608226543441993142957)
              ·
                refine ⟨287103084953790747428609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765608226543441993142957 287103084953790747428609)
                ·
                  refine ⟨215327313715343060571457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287103084953790747428609 215327313715343060571457)
                  ·
                    rfl

theorem cell20_471767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 2].length) (baseStart_471767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471767 prefixEnd_471767 := by exact prefixLift 471767
  have htrace : WordTrace (prefixWord ++ tailWord_471767) baseStart_471767 baseEnd_471767 := by
    simpa [prefixWord, tailWord_471767, baseEnd_471767] using wordTrace_append hprefix tailTrace_471767
  have hstable : (prefixWord ++ tailWord_471767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471767).length < 2 ^ (prefixWord ++ tailWord_471767).sum := by decide
  have hdescent : baseEnd_471767 < baseStart_471767 := by decide
  rcases family_descends (prefixWord ++ tailWord_471767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471781 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_471781 : Nat := 118140960795 + 471781 * 2 ^ 59
def prefixEnd_471781 : Nat := 4983230072969 + 3 ^ 40 * 471781 * 2
def baseEnd_471781 : Nat := 215333703696821234104733

theorem tailTrace_471781 : CollatzResearch.WordTrace tailWord_471781 prefixEnd_471781 215333703696821234104733 := by
  unfold tailWord_471781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17207266703825485625103197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11471511135883657083402131 17207266703825485625103197)
  ·
    refine ⟨6452725013934557109413699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17207266703825485625103197 6452725013934557109413699)
    ·
      refine ⟨9679087520901835664120549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6452725013934557109413699 9679087520901835664120549)
      ·
        refine ⟨1814828910169094187022603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9679087520901835664120549 1814828910169094187022603)
        ·
          refine ⟨2722243365253641280533905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814828910169094187022603 2722243365253641280533905)
          ·
            refine ⟨2041682523940230960400429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2722243365253641280533905 2041682523940230960400429)
            ·
              refine ⟨765630946477586610150161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2041682523940230960400429 765630946477586610150161)
              ·
                refine ⟨574223209858189957612621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765630946477586610150161 574223209858189957612621)
                ·
                  refine ⟨215333703696821234104733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574223209858189957612621 215333703696821234104733)
                  ·
                    rfl

theorem cell20_471781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_471781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471781 prefixEnd_471781 := by exact prefixLift 471781
  have htrace : WordTrace (prefixWord ++ tailWord_471781) baseStart_471781 baseEnd_471781 := by
    simpa [prefixWord, tailWord_471781, baseEnd_471781] using wordTrace_append hprefix tailTrace_471781
  have hstable : (prefixWord ++ tailWord_471781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471781).length < 2 ^ (prefixWord ++ tailWord_471781).sum := by decide
  have hdescent : baseEnd_471781 < baseStart_471781 := by decide
  rcases family_descends (prefixWord ++ tailWord_471781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471798 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_471798 : Nat := 118140960795 + 471798 * 2 ^ 59
def prefixEnd_471798 : Nat := 4983230072969 + 3 ^ 40 * 471798 * 2
def baseEnd_471798 : Nat := 215341462960044730537997

theorem tailTrace_471798 : CollatzResearch.WordTrace tailWord_471798 prefixEnd_471798 215341462960044730537997 := by
  unfold tailWord_471798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075492921547743595529503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11471924496509265018981365 1075492921547743595529503)
  ·
    refine ⟨1613239382321615393294255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1075492921547743595529503 1613239382321615393294255)
    ·
      refine ⟨2419859073482423089941383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613239382321615393294255 2419859073482423089941383)
      ·
        refine ⟨3629788610223634634912075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419859073482423089941383 3629788610223634634912075)
        ·
          refine ⟨5444682915335451952368113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629788610223634634912075 5444682915335451952368113)
          ·
            refine ⟨4083512186501588964276085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5444682915335451952368113 4083512186501588964276085)
            ·
              refine ⟨382829267484523965400883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4083512186501588964276085 382829267484523965400883)
              ·
                refine ⟨574243901226785948101325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382829267484523965400883 574243901226785948101325)
                ·
                  refine ⟨215341462960044730537997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574243901226785948101325 215341462960044730537997)
                  ·
                    rfl

theorem cell20_471798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_471798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471798 prefixEnd_471798 := by exact prefixLift 471798
  have htrace : WordTrace (prefixWord ++ tailWord_471798) baseStart_471798 baseEnd_471798 := by
    simpa [prefixWord, tailWord_471798, baseEnd_471798] using wordTrace_append hprefix tailTrace_471798
  have hstable : (prefixWord ++ tailWord_471798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471798).length < 2 ^ (prefixWord ++ tailWord_471798).sum := by decide
  have hdescent : baseEnd_471798 < baseStart_471798 := by decide
  rcases family_descends (prefixWord ++ tailWord_471798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471802 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_471802 : Nat := 118140960795 + 471802 * 2 ^ 59
def prefixEnd_471802 : Nat := 4983230072969 + 3 ^ 40 * 471802 * 2
def baseEnd_471802 : Nat := 215343288669038494404647

theorem tailTrace_471802 : CollatzResearch.WordTrace tailWord_471802 prefixEnd_471802 215343288669038494404647 := by
  unfold tailWord_471802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302008159187351552904415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11472021757832937474411773 4302008159187351552904415)
  ·
    refine ⟨6453012238781027329356623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4302008159187351552904415 6453012238781027329356623)
    ·
      refine ⟨9679518358171540994034935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453012238781027329356623 9679518358171540994034935)
      ·
        refine ⟨14519277537257311491052403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679518358171540994034935 14519277537257311491052403)
        ·
          refine ⟨21778916305885967236578605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519277537257311491052403 21778916305885967236578605)
          ·
            refine ⟨8167093614707237713716977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21778916305885967236578605 8167093614707237713716977)
            ·
              refine ⟨6125320211030428285287733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8167093614707237713716977 6125320211030428285287733)
              ·
                refine ⟨574248769784102651745725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6125320211030428285287733 574248769784102651745725)
                ·
                  refine ⟨215343288669038494404647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574248769784102651745725 215343288669038494404647)
                  ·
                    rfl

theorem cell20_471802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_471802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471802 prefixEnd_471802 := by exact prefixLift 471802
  have htrace : WordTrace (prefixWord ++ tailWord_471802) baseStart_471802 baseEnd_471802 := by
    simpa [prefixWord, tailWord_471802, baseEnd_471802] using wordTrace_append hprefix tailTrace_471802
  have hstable : (prefixWord ++ tailWord_471802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471802).length < 2 ^ (prefixWord ++ tailWord_471802).sum := by decide
  have hdescent : baseEnd_471802 < baseStart_471802 := by decide
  rcases family_descends (prefixWord ++ tailWord_471802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471823 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_471823 : Nat := 118140960795 + 471823 * 2 ^ 59
def prefixEnd_471823 : Nat := 4983230072969 + 3 ^ 40 * 471823 * 2
def baseEnd_471823 : Nat := 215352873641255754704561

theorem tailTrace_471823 : CollatzResearch.WordTrace tailWord_471823 prefixEnd_471823 215352873641255754704561 := by
  unfold tailWord_471823
  simp only [CollatzResearch.WordTrace]
  refine ⟨17208798569673326798132123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11472532379782217865421415 17208798569673326798132123)
  ·
    refine ⟨25813197854509990197198185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17208798569673326798132123 25813197854509990197198185)
    ·
      refine ⟨19359898390882492647898639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25813197854509990197198185 19359898390882492647898639)
      ·
        refine ⟨29039847586323738971847959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19359898390882492647898639 29039847586323738971847959)
        ·
          refine ⟨43559771379485608457771939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29039847586323738971847959 43559771379485608457771939)
          ·
            refine ⟨65339657069228412686657909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43559771379485608457771939 65339657069228412686657909)
            ·
              refine ⟨6125592850240163689374179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65339657069228412686657909 6125592850240163689374179)
              ·
                refine ⟨9188389275360245534061269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125592850240163689374179 9188389275360245534061269)
                ·
                  refine ⟨215352873641255754704561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9188389275360245534061269 215352873641255754704561)
                  ·
                    rfl

theorem cell20_471823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_471823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471823 prefixEnd_471823 := by exact prefixLift 471823
  have htrace : WordTrace (prefixWord ++ tailWord_471823) baseStart_471823 baseEnd_471823 := by
    simpa [prefixWord, tailWord_471823, baseEnd_471823] using wordTrace_append hprefix tailTrace_471823
  have hstable : (prefixWord ++ tailWord_471823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471823).length < 2 ^ (prefixWord ++ tailWord_471823).sum := by decide
  have hdescent : baseEnd_471823 < baseStart_471823 := by decide
  rcases family_descends (prefixWord ++ tailWord_471823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471840 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_471840 : Nat := 118140960795 + 471840 * 2 ^ 59
def prefixEnd_471840 : Nat := 4983230072969 + 3 ^ 40 * 471840 * 2
def baseEnd_471840 : Nat := 215360632904479251137825

theorem tailTrace_471840 : CollatzResearch.WordTrace tailWord_471840 prefixEnd_471840 215360632904479251137825 := by
  unfold tailWord_471840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8604709305305869350750487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11472945740407825801000649 8604709305305869350750487)
  ·
    refine ⟨12907063957958804026125731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8604709305305869350750487 12907063957958804026125731)
    ·
      refine ⟨19360595936938206039188597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907063957958804026125731 19360595936938206039188597)
      ·
        refine ⟨1815055869087956816173931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19360595936938206039188597 1815055869087956816173931)
        ·
          refine ⟨2722583803631935224260897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815055869087956816173931 2722583803631935224260897)
          ·
            refine ⟨2041937852723951418195673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2722583803631935224260897 2041937852723951418195673)
            ·
              refine ⟨1531453389542963563646755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041937852723951418195673 1531453389542963563646755)
              ·
                refine ⟨2297180084314445345470133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531453389542963563646755 2297180084314445345470133)
                ·
                  refine ⟨215360632904479251137825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2297180084314445345470133 215360632904479251137825)
                  ·
                    rfl

theorem cell20_471840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_471840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471840 prefixEnd_471840 := by exact prefixLift 471840
  have htrace : WordTrace (prefixWord ++ tailWord_471840) baseStart_471840 baseEnd_471840 := by
    simpa [prefixWord, tailWord_471840, baseEnd_471840] using wordTrace_append hprefix tailTrace_471840
  have hstable : (prefixWord ++ tailWord_471840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471840).length < 2 ^ (prefixWord ++ tailWord_471840).sum := by decide
  have hdescent : baseEnd_471840 < baseStart_471840 := by decide
  rcases family_descends (prefixWord ++ tailWord_471840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471853 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 3]
def baseStart_471853 : Nat := 118140960795 + 471853 * 2 ^ 59
def prefixEnd_471853 : Nat := 4983230072969 + 3 ^ 40 * 471853 * 2
def baseEnd_471853 : Nat := 215366566458708983704439

theorem tailTrace_471853 : CollatzResearch.WordTrace tailWord_471853 prefixEnd_471853 215366566458708983704439 := by
  unfold tailWord_471853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209892759564641921724213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11473261839709761281149475 17209892759564641921724213)
  ·
    refine ⟨1613427446209185180161645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17209892759564641921724213 1613427446209185180161645)
    ·
      refine ⟨605035292328444442560617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1613427446209185180161645 605035292328444442560617)
      ·
        refine ⟨453776469246333331920463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605035292328444442560617 453776469246333331920463)
        ·
          refine ⟨680664703869499997880695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453776469246333331920463 680664703869499997880695)
          ·
            refine ⟨1020997055804249996821043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680664703869499997880695 1020997055804249996821043)
            ·
              refine ⟨1531495583706374995231565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020997055804249996821043 1531495583706374995231565)
              ·
                refine ⟨574310843889890623211837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1531495583706374995231565 574310843889890623211837)
                ·
                  refine ⟨215366566458708983704439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574310843889890623211837 215366566458708983704439)
                  ·
                    rfl

theorem cell20_471853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_471853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471853 prefixEnd_471853 := by exact prefixLift 471853
  have htrace : WordTrace (prefixWord ++ tailWord_471853) baseStart_471853 baseEnd_471853 := by
    simpa [prefixWord, tailWord_471853, baseEnd_471853] using wordTrace_append hprefix tailTrace_471853
  have hstable : (prefixWord ++ tailWord_471853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471853).length < 2 ^ (prefixWord ++ tailWord_471853).sum := by decide
  have hdescent : baseEnd_471853 < baseStart_471853 := by decide
  rcases family_descends (prefixWord ++ tailWord_471853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471892 : List Nat := [2, 4, 1, 1, 12]
def baseStart_471892 : Nat := 118140960795 + 471892 * 2 ^ 59
def prefixEnd_471892 : Nat := 4983230072969 + 3 ^ 40 * 471892 * 2
def baseEnd_471892 : Nat := 2659066260758002239559

theorem tailTrace_471892 : CollatzResearch.WordTrace tailWord_471892 prefixEnd_471892 2659066260758002239559 := by
  unfold tailWord_471892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605657603211675791196965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11474210137615567721595953 8605657603211675791196965)
  ·
    refine ⟨1613560800602189210849431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8605657603211675791196965 1613560800602189210849431)
    ·
      refine ⟨2420341200903283816274147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613560800602189210849431 2420341200903283816274147)
      ·
        refine ⟨3630511801354925724411221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420341200903283816274147 3630511801354925724411221)
        ·
          refine ⟨2659066260758002239559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3630511801354925724411221 2659066260758002239559)
          ·
            rfl

theorem cell20_471892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 12].length) (baseStart_471892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471892 prefixEnd_471892 := by exact prefixLift 471892
  have htrace : WordTrace (prefixWord ++ tailWord_471892) baseStart_471892 baseEnd_471892 := by
    simpa [prefixWord, tailWord_471892, baseEnd_471892] using wordTrace_append hprefix tailTrace_471892
  have hstable : (prefixWord ++ tailWord_471892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471892).length < 2 ^ (prefixWord ++ tailWord_471892).sum := by decide
  have hdescent : baseEnd_471892 < baseStart_471892 := by decide
  rcases family_descends (prefixWord ++ tailWord_471892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471895 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_471895 : Nat := 118140960795 + 471895 * 2 ^ 59
def prefixEnd_471895 : Nat := 4983230072969 + 3 ^ 40 * 471895 * 2
def baseEnd_471895 : Nat := 215385736403143504304267

theorem tailTrace_471895 : CollatzResearch.WordTrace tailWord_471895 prefixEnd_471895 215385736403143504304267 := by
  unfold tailWord_471895
  simp only [CollatzResearch.WordTrace]
  refine ⟨17211424625412483094753139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11474283083608322063168759 17211424625412483094753139)
  ·
    refine ⟨25817136938118724642129709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17211424625412483094753139 25817136938118724642129709)
    ·
      refine ⟨9681426351794521740798641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25817136938118724642129709 9681426351794521740798641)
      ·
        refine ⟨7261069763845891305598981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9681426351794521740798641 7261069763845891305598981)
        ·
          refine ⟨1361450580721104619799809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7261069763845891305598981 1361450580721104619799809)
          ·
            refine ⟨1021087935540828464849857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361450580721104619799809 1021087935540828464849857)
            ·
              refine ⟨765815951655621348637393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021087935540828464849857 765815951655621348637393)
              ·
                refine ⟨574361963741716011478045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765815951655621348637393 574361963741716011478045)
                ·
                  refine ⟨215385736403143504304267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574361963741716011478045 215385736403143504304267)
                  ·
                    rfl

theorem cell20_471895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_471895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471895 prefixEnd_471895 := by exact prefixLift 471895
  have htrace : WordTrace (prefixWord ++ tailWord_471895) baseStart_471895 baseEnd_471895 := by
    simpa [prefixWord, tailWord_471895, baseEnd_471895] using wordTrace_append hprefix tailTrace_471895
  have hstable : (prefixWord ++ tailWord_471895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471895).length < 2 ^ (prefixWord ++ tailWord_471895).sum := by decide
  have hdescent : baseEnd_471895 < baseStart_471895 := by decide
  rcases family_descends (prefixWord ++ tailWord_471895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471898 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_471898 : Nat := 118140960795 + 471898 * 2 ^ 59
def prefixEnd_471898 : Nat := 4983230072969 + 3 ^ 40 * 471898 * 2
def baseEnd_471898 : Nat := 215387105684888827204255

theorem tailTrace_471898 : CollatzResearch.WordTrace tailWord_471898 prefixEnd_471898 215387105684888827204255 := by
  unfold tailWord_471898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302883511100403651778087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11474356029601076404741565 4302883511100403651778087)
  ·
    refine ⟨6454325266650605477667131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4302883511100403651778087 6454325266650605477667131)
    ·
      refine ⟨9681487899975908216500697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6454325266650605477667131 9681487899975908216500697)
      ·
        refine ⟨7261115924981931162375523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9681487899975908216500697 7261115924981931162375523)
        ·
          refine ⟨10891673887472896743563285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261115924981931162375523 10891673887472896743563285)
          ·
            refine ⟨510547213475292034854529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10891673887472896743563285 510547213475292034854529)
            ·
              refine ⟨382910410106469026140897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510547213475292034854529 382910410106469026140897)
              ·
                refine ⟨287182807579851769605673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382910410106469026140897 287182807579851769605673)
                ·
                  refine ⟨215387105684888827204255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287182807579851769605673 215387105684888827204255)
                  ·
                    rfl

theorem cell20_471898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_471898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471898 prefixEnd_471898 := by exact prefixLift 471898
  have htrace : WordTrace (prefixWord ++ tailWord_471898) baseStart_471898 baseEnd_471898 := by
    simpa [prefixWord, tailWord_471898, baseEnd_471898] using wordTrace_append hprefix tailTrace_471898
  have hstable : (prefixWord ++ tailWord_471898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471898).length < 2 ^ (prefixWord ++ tailWord_471898).sum := by decide
  have hdescent : baseEnd_471898 < baseStart_471898 := by decide
  rcases family_descends (prefixWord ++ tailWord_471898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471916 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_471916 : Nat := 118140960795 + 471916 * 2 ^ 59
def prefixEnd_471916 : Nat := 4983230072969 + 3 ^ 40 * 471916 * 2
def baseEnd_471916 : Nat := 215395321375360764604181

theorem tailTrace_471916 : CollatzResearch.WordTrace tailWord_471916 prefixEnd_471916 215395321375360764604181 := by
  unfold tailWord_471916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8606095279168201840633801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11474793705557602454178401 8606095279168201840633801)
  ·
    refine ⟨6454571459376151380475351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8606095279168201840633801 6454571459376151380475351)
    ·
      refine ⟨9681857189064227070713027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6454571459376151380475351 9681857189064227070713027)
      ·
        refine ⟨14522785783596340606069541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9681857189064227070713027 14522785783596340606069541)
        ·
          refine ⟨2723022334424313863638039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14522785783596340606069541 2723022334424313863638039)
          ·
            refine ⟨4084533501636470795457059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723022334424313863638039 4084533501636470795457059)
            ·
              refine ⟨6126800252454706193185589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084533501636470795457059 6126800252454706193185589)
              ·
                refine ⟨574387523667628705611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6126800252454706193185589 574387523667628705611149)
                ·
                  refine ⟨215395321375360764604181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574387523667628705611149 215395321375360764604181)
                  ·
                    rfl

theorem cell20_471916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_471916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471916 prefixEnd_471916 := by exact prefixLift 471916
  have htrace : WordTrace (prefixWord ++ tailWord_471916) baseStart_471916 baseEnd_471916 := by
    simpa [prefixWord, tailWord_471916, baseEnd_471916] using wordTrace_append hprefix tailTrace_471916
  have hstable : (prefixWord ++ tailWord_471916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471916).length < 2 ^ (prefixWord ++ tailWord_471916).sum := by decide
  have hdescent : baseEnd_471916 < baseStart_471916 := by decide
  rcases family_descends (prefixWord ++ tailWord_471916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471985 : List Nat := [1, 2, 2, 4, 3, 1, 1, 6]
def baseStart_471985 : Nat := 118140960795 + 471985 * 2 ^ 59
def prefixEnd_471985 : Nat := 4983230072969 + 3 ^ 40 * 471985 * 2
def baseEnd_471985 : Nat := 71808938285167730434633

theorem tailTrace_471985 : CollatzResearch.WordTrace tailWord_471985 prefixEnd_471985 71808938285167730434633 := by
  unfold tailWord_471985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214707195086428465529409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11476471463390952310352939 17214707195086428465529409)
  ·
    refine ⟨12911030396314821349147057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17214707195086428465529409 12911030396314821349147057)
    ·
      refine ⟨9683272797236116011860293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12911030396314821349147057 9683272797236116011860293)
      ·
        refine ⟨1815613649481771752223805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9683272797236116011860293 1815613649481771752223805)
        ·
          refine ⟨680855118555664407083927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1815613649481771752223805 680855118555664407083927)
          ·
            refine ⟨1021282677833496610625891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680855118555664407083927 1021282677833496610625891)
            ·
              refine ⟨1531924016750244915938837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021282677833496610625891 1531924016750244915938837)
              ·
                refine ⟨71808938285167730434633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1531924016750244915938837 71808938285167730434633)
                ·
                  rfl

theorem cell20_471985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_471985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_471985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_471985 prefixEnd_471985 := by exact prefixLift 471985
  have htrace : WordTrace (prefixWord ++ tailWord_471985) baseStart_471985 baseEnd_471985 := by
    simpa [prefixWord, tailWord_471985, baseEnd_471985] using wordTrace_append hprefix tailTrace_471985
  have hstable : (prefixWord ++ tailWord_471985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471985).length < 2 ^ (prefixWord ++ tailWord_471985).sum := by decide
  have hdescent : baseEnd_471985 < baseStart_471985 := by decide
  rcases family_descends (prefixWord ++ tailWord_471985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472026 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_472026 : Nat := 118140960795 + 472026 * 2 ^ 59
def prefixEnd_472026 : Nat := 4983230072969 + 3 ^ 40 * 472026 * 2
def baseEnd_472026 : Nat := 215445528372689270937065

theorem tailTrace_472026 : CollatzResearch.WordTrace tailWord_472026 prefixEnd_472026 215445528372689270937065 := by
  unfold tailWord_472026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304050646984473116942983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11477468391958594978514621 4304050646984473116942983)
  ·
    refine ⟨6456075970476709675414475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4304050646984473116942983 6456075970476709675414475)
    ·
      refine ⟨9684113955715064513121713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6456075970476709675414475 9684113955715064513121713)
      ·
        refine ⟨7263085466786298384841285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9684113955715064513121713 7263085466786298384841285)
        ·
          refine ⟨1361828525022430947157741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7263085466786298384841285 1361828525022430947157741)
          ·
            refine ⟨510685696883411605184153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1361828525022430947157741 510685696883411605184153)
            ·
              refine ⟨383014272662558703888115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510685696883411605184153 383014272662558703888115)
              ·
                refine ⟨574521408993838055832173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383014272662558703888115 574521408993838055832173)
                ·
                  refine ⟨215445528372689270937065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 574521408993838055832173 215445528372689270937065)
                  ·
                    rfl

theorem cell20_472026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_472026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472026 prefixEnd_472026 := by exact prefixLift 472026
  have htrace : WordTrace (prefixWord ++ tailWord_472026) baseStart_472026 baseEnd_472026 := by
    simpa [prefixWord, tailWord_472026, baseEnd_472026] using wordTrace_append hprefix tailTrace_472026
  have hstable : (prefixWord ++ tailWord_472026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472026).length < 2 ^ (prefixWord ++ tailWord_472026).sum := by decide
  have hdescent : baseEnd_472026 < baseStart_472026 := by decide
  rcases family_descends (prefixWord ++ tailWord_472026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472092 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_472092 : Nat := 118140960795 + 472092 * 2 ^ 59
def prefixEnd_472092 : Nat := 4983230072969 + 3 ^ 40 * 472092 * 2
def baseEnd_472092 : Nat := 215475652571086374736795

theorem tailTrace_472092 : CollatzResearch.WordTrace tailWord_472092 prefixEnd_472092 215475652571086374736795 := by
  unfold tailWord_472092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609304902849392869837265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11479073203799190493116353 8609304902849392869837265)
  ·
    refine ⟨6456978677137044652377949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8609304902849392869837265 6456978677137044652377949)
    ·
      refine ⟨2421367003926391744641731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6456978677137044652377949 2421367003926391744641731)
      ·
        refine ⟨3632050505889587616962597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421367003926391744641731 3632050505889587616962597)
        ·
          refine ⟨681009469854297678180487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3632050505889587616962597 681009469854297678180487)
          ·
            refine ⟨1021514204781446517270731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681009469854297678180487 1021514204781446517270731)
            ·
              refine ⟨1532271307172169775906097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021514204781446517270731 1532271307172169775906097)
              ·
                refine ⟨1149203480379127331929573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532271307172169775906097 1149203480379127331929573)
                ·
                  refine ⟨215475652571086374736795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149203480379127331929573 215475652571086374736795)
                  ·
                    rfl

theorem cell20_472092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_472092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472092 prefixEnd_472092 := by exact prefixLift 472092
  have htrace : WordTrace (prefixWord ++ tailWord_472092) baseStart_472092 baseEnd_472092 := by
    simpa [prefixWord, tailWord_472092, baseEnd_472092] using wordTrace_append hprefix tailTrace_472092
  have hstable : (prefixWord ++ tailWord_472092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472092).length < 2 ^ (prefixWord ++ tailWord_472092).sum := by decide
  have hdescent : baseEnd_472092 < baseStart_472092 := by decide
  rcases family_descends (prefixWord ++ tailWord_472092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472099 : List Nat := [1, 1, 1, 4, 3, 3, 3, 4]
def baseStart_472099 : Nat := 118140960795 + 472099 * 2 ^ 59
def prefixEnd_472099 : Nat := 4983230072969 + 3 ^ 40 * 472099 * 2
def baseEnd_472099 : Nat := 71826282520608487167811

theorem tailTrace_472099 : CollatzResearch.WordTrace tailWord_472099 prefixEnd_472099 71826282520608487167811 := by
  unfold tailWord_472099
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218865116673425935179351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11479243411115617290119567 17218865116673425935179351)
  ·
    refine ⟨25828297675010138902769027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17218865116673425935179351 25828297675010138902769027)
    ·
      refine ⟨38742446512515208354153541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25828297675010138902769027 38742446512515208354153541)
      ·
        refine ⟨7264208721096601566403789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38742446512515208354153541 7264208721096601566403789)
        ·
          refine ⟨2724078270411225587401421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7264208721096601566403789 2724078270411225587401421)
          ·
            refine ⟨1021529351404209595275533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2724078270411225587401421 1021529351404209595275533)
            ·
              refine ⟨383073506776578598228325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1021529351404209595275533 383073506776578598228325)
              ·
                refine ⟨71826282520608487167811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383073506776578598228325 71826282520608487167811)
                ·
                  rfl

theorem cell20_472099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_472099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472099 prefixEnd_472099 := by exact prefixLift 472099
  have htrace : WordTrace (prefixWord ++ tailWord_472099) baseStart_472099 baseEnd_472099 := by
    simpa [prefixWord, tailWord_472099, baseEnd_472099] using wordTrace_append hprefix tailTrace_472099
  have hstable : (prefixWord ++ tailWord_472099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472099).length < 2 ^ (prefixWord ++ tailWord_472099).sum := by decide
  have hdescent : baseEnd_472099 < baseStart_472099 := by decide
  rcases family_descends (prefixWord ++ tailWord_472099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472120 : List Nat := [2, 1, 2, 1, 5, 2, 7]
def baseStart_472120 : Nat := 118140960795 + 472120 * 2 ^ 59
def prefixEnd_472120 : Nat := 4983230072969 + 3 ^ 40 * 472120 * 2
def baseEnd_472120 : Nat := 23943159170449191311483

theorem tailTrace_472120 : CollatzResearch.WordTrace tailWord_472120 prefixEnd_472120 23943159170449191311483 := by
  unfold tailWord_472120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609815524798673260846907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11479754033064897681129209 8609815524798673260846907)
  ·
    refine ⟨12914723287198009891270361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8609815524798673260846907 12914723287198009891270361)
    ·
      refine ⟨9686042465398507418452771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12914723287198009891270361 9686042465398507418452771)
      ·
        refine ⟨14529063698097761127679157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9686042465398507418452771 14529063698097761127679157)
        ·
          refine ⟨1362099721696665105719921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14529063698097761127679157 1362099721696665105719921)
          ·
            refine ⟨1021574791272498829289941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1362099721696665105719921 1021574791272498829289941)
            ·
              refine ⟨23943159170449191311483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1021574791272498829289941 23943159170449191311483)
              ·
                rfl

theorem cell20_472120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_472120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472120 prefixEnd_472120 := by exact prefixLift 472120
  have htrace : WordTrace (prefixWord ++ tailWord_472120) baseStart_472120 baseEnd_472120 := by
    simpa [prefixWord, tailWord_472120, baseEnd_472120] using wordTrace_append hprefix tailTrace_472120
  have hstable : (prefixWord ++ tailWord_472120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472120).length < 2 ^ (prefixWord ++ tailWord_472120).sum := by decide
  have hdescent : baseEnd_472120 < baseStart_472120 := by decide
  rcases family_descends (prefixWord ++ tailWord_472120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472150 : List Nat := [5, 2, 2, 1, 2, 2, 2, 4]
def baseStart_472150 : Nat := 118140960795 + 472150 * 2 ^ 59
def prefixEnd_472150 : Nat := 4983230072969 + 3 ^ 40 * 472150 * 2
def baseEnd_472150 : Nat := 71834041783831983601075

theorem tailTrace_472150 : CollatzResearch.WordTrace tailWord_472150 prefixEnd_472150 71834041783831983601075 := by
  unfold tailWord_472150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076295327468041352830369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11480483492992441096857269 1076295327468041352830369)
  ·
    refine ⟨807221495601031014622777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1076295327468041352830369 807221495601031014622777)
    ·
      refine ⟨605416121700773260967083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807221495601031014622777 605416121700773260967083)
      ·
        refine ⟨908124182551159891450625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605416121700773260967083 908124182551159891450625)
        ·
          refine ⟨681093136913369918587969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908124182551159891450625 681093136913369918587969)
          ·
            refine ⟨510819852685027438940977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681093136913369918587969 510819852685027438940977)
            ·
              refine ⟨383114889513770579205733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510819852685027438940977 383114889513770579205733)
              ·
                refine ⟨71834041783831983601075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383114889513770579205733 71834041783831983601075)
                ·
                  rfl

theorem cell20_472150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_472150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472150 prefixEnd_472150 := by exact prefixLift 472150
  have htrace : WordTrace (prefixWord ++ tailWord_472150) baseStart_472150 baseEnd_472150 := by
    simpa [prefixWord, tailWord_472150, baseEnd_472150] using wordTrace_append hprefix tailTrace_472150
  have hstable : (prefixWord ++ tailWord_472150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472150).length < 2 ^ (prefixWord ++ tailWord_472150).sum := by decide
  have hdescent : baseEnd_472150 < baseStart_472150 := by decide
  rcases family_descends (prefixWord ++ tailWord_472150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472165 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_472165 : Nat := 118140960795 + 472165 * 2 ^ 59
def prefixEnd_472165 : Nat := 4983230072969 + 3 ^ 40 * 472165 * 2
def baseEnd_472165 : Nat := 215508971760222565303163

theorem tailTrace_472165 : CollatzResearch.WordTrace tailWord_472165 prefixEnd_472165 215508971760222565303163 := by
  unfold tailWord_472165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221272334434319207081949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11480848222956212804721299 17221272334434319207081949)
  ·
    refine ⟨6457977125412869702655731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17221272334434319207081949 6457977125412869702655731)
    ·
      refine ⟨9686965688119304553983597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457977125412869702655731 9686965688119304553983597)
      ·
        refine ⟨3632612133044739207743849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9686965688119304553983597 3632612133044739207743849)
        ·
          refine ⟨2724459099783554405807887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632612133044739207743849 2724459099783554405807887)
          ·
            refine ⟨4086688649675331608711831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724459099783554405807887 4086688649675331608711831)
            ·
              refine ⟨6130032974512997413067747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086688649675331608711831 6130032974512997413067747)
              ·
                refine ⟨9195049461769496119601621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130032974512997413067747 9195049461769496119601621)
                ·
                  refine ⟨215508971760222565303163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9195049461769496119601621 215508971760222565303163)
                  ·
                    rfl

theorem cell20_472165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_472165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472165 prefixEnd_472165 := by exact prefixLift 472165
  have htrace : WordTrace (prefixWord ++ tailWord_472165) baseStart_472165 baseEnd_472165 := by
    simpa [prefixWord, tailWord_472165, baseEnd_472165] using wordTrace_append hprefix tailTrace_472165
  have hstable : (prefixWord ++ tailWord_472165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472165).length < 2 ^ (prefixWord ++ tailWord_472165).sum := by decide
  have hdescent : baseEnd_472165 < baseStart_472165 := by decide
  rcases family_descends (prefixWord ++ tailWord_472165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472181 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 2]
def baseStart_472181 : Nat := 118140960795 + 472181 * 2 ^ 59
def prefixEnd_472181 : Nat := 4983230072969 + 3 ^ 40 * 472181 * 2
def baseEnd_472181 : Nat := 215516274596197620769765

theorem tailTrace_472181 : CollatzResearch.WordTrace tailWord_472181 prefixEnd_472181 215516274596197620769765 := by
  unfold tailWord_472181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221855902376353939664397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11481237268250902626442931 17221855902376353939664397)
  ·
    refine ⟨6458195963391132727374149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17221855902376353939664397 6458195963391132727374149)
    ·
      refine ⟨1210911743135837386382653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6458195963391132727374149 1210911743135837386382653)
      ·
        refine ⟨454091903675939019893495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1210911743135837386382653 454091903675939019893495)
        ·
          refine ⟨681137855513908529840243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454091903675939019893495 681137855513908529840243)
          ·
            refine ⟨1021706783270862794760365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681137855513908529840243 1021706783270862794760365)
            ·
              refine ⟨383140043726573548035137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1021706783270862794760365 383140043726573548035137)
              ·
                refine ⟨287355032794930161026353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383140043726573548035137 287355032794930161026353)
                ·
                  refine ⟨215516274596197620769765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287355032794930161026353 215516274596197620769765)
                  ·
                    rfl

theorem cell20_472181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_472181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472181 prefixEnd_472181 := by exact prefixLift 472181
  have htrace : WordTrace (prefixWord ++ tailWord_472181) baseStart_472181 baseEnd_472181 := by
    simpa [prefixWord, tailWord_472181, baseEnd_472181] using wordTrace_append hprefix tailTrace_472181
  have hstable : (prefixWord ++ tailWord_472181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472181).length < 2 ^ (prefixWord ++ tailWord_472181).sum := by decide
  have hdescent : baseEnd_472181 < baseStart_472181 := by decide
  rcases family_descends (prefixWord ++ tailWord_472181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472182 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_472182 : Nat := 118140960795 + 472182 * 2 ^ 59
def prefixEnd_472182 : Nat := 4983230072969 + 3 ^ 40 * 472182 * 2
def baseEnd_472182 : Nat := 215516731023446061736427

theorem tailTrace_472182 : CollatzResearch.WordTrace tailWord_472182 prefixEnd_472182 215516731023446061736427 := by
  unfold tailWord_472182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076368273460795694403175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11481261583581820740300533 1076368273460795694403175)
  ·
    refine ⟨1614552410191193541604763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076368273460795694403175 1614552410191193541604763)
    ·
      refine ⟨2421828615286790312407145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614552410191193541604763 2421828615286790312407145)
      ·
        refine ⟨1816371461465092734305359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2421828615286790312407145 1816371461465092734305359)
        ·
          refine ⟨2724557192197639101458039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816371461465092734305359 2724557192197639101458039)
          ·
            refine ⟨4086835788296458652187059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724557192197639101458039 4086835788296458652187059)
            ·
              refine ⟨6130253682444687978280589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086835788296458652187059 6130253682444687978280589)
              ·
                refine ⟨2298845130916757991855221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6130253682444687978280589 2298845130916757991855221)
                ·
                  refine ⟨215516731023446061736427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2298845130916757991855221 215516731023446061736427)
                  ·
                    rfl

theorem cell20_472182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_472182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472182 prefixEnd_472182 := by exact prefixLift 472182
  have htrace : WordTrace (prefixWord ++ tailWord_472182) baseStart_472182 baseEnd_472182 := by
    simpa [prefixWord, tailWord_472182, baseEnd_472182] using wordTrace_append hprefix tailTrace_472182
  have hstable : (prefixWord ++ tailWord_472182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472182).length < 2 ^ (prefixWord ++ tailWord_472182).sum := by decide
  have hdescent : baseEnd_472182 < baseStart_472182 := by decide
  rcases family_descends (prefixWord ++ tailWord_472182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472185 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 4]
def baseStart_472185 : Nat := 118140960795 + 472185 * 2 ^ 59
def prefixEnd_472185 : Nat := 4983230072969 + 3 ^ 40 * 472185 * 2
def baseEnd_472185 : Nat := 215518100305191384636415

theorem tailTrace_472185 : CollatzResearch.WordTrace tailWord_472185 prefixEnd_472185 215518100305191384636415 := by
  unfold tailWord_472185
  simp only [CollatzResearch.WordTrace]
  refine ⟨17222001794361862622810009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11481334529574575081873339 17222001794361862622810009)
  ·
    refine ⟨12916501345771396967107507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17222001794361862622810009 12916501345771396967107507)
    ·
      refine ⟨19374752018657095450661261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12916501345771396967107507 19374752018657095450661261)
      ·
        refine ⟨7265532006996410793997973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19374752018657095450661261 7265532006996410793997973)
        ·
          refine ⟨340571812827956755968655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7265532006996410793997973 340571812827956755968655)
          ·
            refine ⟨510857719241935133952983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340571812827956755968655 510857719241935133952983)
            ·
              refine ⟨766286578862902700929475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510857719241935133952983 766286578862902700929475)
              ·
                refine ⟨1149429868294354051394213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766286578862902700929475 1149429868294354051394213)
                ·
                  refine ⟨215518100305191384636415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149429868294354051394213 215518100305191384636415)
                  ·
                    rfl

theorem cell20_472185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_472185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472185 prefixEnd_472185 := by exact prefixLift 472185
  have htrace : WordTrace (prefixWord ++ tailWord_472185) baseStart_472185 baseEnd_472185 := by
    simpa [prefixWord, tailWord_472185, baseEnd_472185] using wordTrace_append hprefix tailTrace_472185
  have hstable : (prefixWord ++ tailWord_472185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472185).length < 2 ^ (prefixWord ++ tailWord_472185).sum := by decide
  have hdescent : baseEnd_472185 < baseStart_472185 := by decide
  rcases family_descends (prefixWord ++ tailWord_472185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472196 : List Nat := [2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_472196 : Nat := 118140960795 + 472196 * 2 ^ 59
def prefixEnd_472196 : Nat := 4983230072969 + 3 ^ 40 * 472196 * 2
def baseEnd_472196 : Nat := 71841040334974745089901

theorem tailTrace_472196 : CollatzResearch.WordTrace tailWord_472196 prefixEnd_472196 71841040334974745089901 := by
  unfold tailWord_472196
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611201498661005750730221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11481601998214674334306961 8611201498661005750730221)
  ·
    refine ⟨3229200561997877156523833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8611201498661005750730221 3229200561997877156523833)
    ·
      refine ⟨2421900421498407867392875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3229200561997877156523833 2421900421498407867392875)
      ·
        refine ⟨3632850632247611801089313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421900421498407867392875 3632850632247611801089313)
        ·
          refine ⟨2724637974185708850816985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632850632247611801089313 2724637974185708850816985)
          ·
            refine ⟨2043478480639281638112739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2724637974185708850816985 2043478480639281638112739)
            ·
              refine ⟨3065217720958922457169109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043478480639281638112739 3065217720958922457169109)
              ·
                refine ⟨71841040334974745089901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3065217720958922457169109 71841040334974745089901)
                ·
                  rfl

theorem cell20_472196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_472196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472196 prefixEnd_472196 := by exact prefixLift 472196
  have htrace : WordTrace (prefixWord ++ tailWord_472196) baseStart_472196 baseEnd_472196 := by
    simpa [prefixWord, tailWord_472196, baseEnd_472196] using wordTrace_append hprefix tailTrace_472196
  have hstable : (prefixWord ++ tailWord_472196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472196).length < 2 ^ (prefixWord ++ tailWord_472196).sum := by decide
  have hdescent : baseEnd_472196 < baseStart_472196 := by decide
  rcases family_descends (prefixWord ++ tailWord_472196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472310 : List Nat := [5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_472310 : Nat := 118140960795 + 472310 * 2 ^ 59
def prefixEnd_472310 : Nat := 4983230072969 + 3 ^ 40 * 472310 * 2
def baseEnd_472310 : Nat := 71858384570415501823079

theorem tailTrace_472310 : CollatzResearch.WordTrace tailWord_472310 prefixEnd_472310 71858384570415501823079 := by
  unfold tailWord_472310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076660057431813060694399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11484373945939339314073589 1076660057431813060694399)
  ·
    refine ⟨1614990086147719591041599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076660057431813060694399 1614990086147719591041599)
    ·
      refine ⟨2422485129221579386562399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614990086147719591041599 2422485129221579386562399)
      ·
        refine ⟨3633727693832369079843599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2422485129221579386562399 3633727693832369079843599)
        ·
          refine ⟨5450591540748553619765399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633727693832369079843599 5450591540748553619765399)
          ·
            refine ⟨8175887311122830429648099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450591540748553619765399 8175887311122830429648099)
            ·
              refine ⟨12263830966684245644472149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8175887311122830429648099 12263830966684245644472149)
              ·
                refine ⟨71858384570415501823079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12263830966684245644472149 71858384570415501823079)
                ·
                  rfl

theorem cell20_472310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_472310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472310 prefixEnd_472310 := by exact prefixLift 472310
  have htrace : WordTrace (prefixWord ++ tailWord_472310) baseStart_472310 baseEnd_472310 := by
    simpa [prefixWord, tailWord_472310, baseEnd_472310] using wordTrace_append hprefix tailTrace_472310
  have hstable : (prefixWord ++ tailWord_472310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472310).length < 2 ^ (prefixWord ++ tailWord_472310).sum := by decide
  have hdescent : baseEnd_472310 < baseStart_472310 := by decide
  rcases family_descends (prefixWord ++ tailWord_472310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472354 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_472354 : Nat := 118140960795 + 472354 * 2 ^ 59
def prefixEnd_472354 : Nat := 4983230072969 + 3 ^ 40 * 472354 * 2
def baseEnd_472354 : Nat := 215595236510177908002391

theorem tailTrace_472354 : CollatzResearch.WordTrace tailWord_472354 prefixEnd_472354 215595236510177908002391 := by
  unfold tailWord_472354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307041432687401121428029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11485443820499736323808077 4307041432687401121428029)
  ·
    refine ⟨1615140537257775420535511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4307041432687401121428029 1615140537257775420535511)
    ·
      refine ⟨2422710805886663130803267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1615140537257775420535511 2422710805886663130803267)
      ·
        refine ⟨3634066208829994696204901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2422710805886663130803267 3634066208829994696204901)
        ·
          refine ⟨681387414155624005538419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3634066208829994696204901 681387414155624005538419)
          ·
            refine ⟨1022081121233436008307629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681387414155624005538419 1022081121233436008307629)
            ·
              refine ⟨383280420462538503115361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1022081121233436008307629 383280420462538503115361)
              ·
                refine ⟨287460315346903877336521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383280420462538503115361 287460315346903877336521)
                ·
                  refine ⟨215595236510177908002391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287460315346903877336521 215595236510177908002391)
                  ·
                    rfl

theorem cell20_472354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_472354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472354 prefixEnd_472354 := by exact prefixLift 472354
  have htrace : WordTrace (prefixWord ++ tailWord_472354) baseStart_472354 baseEnd_472354 := by
    simpa [prefixWord, tailWord_472354, baseEnd_472354] using wordTrace_append hprefix tailTrace_472354
  have hstable : (prefixWord ++ tailWord_472354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472354).length < 2 ^ (prefixWord ++ tailWord_472354).sum := by decide
  have hdescent : baseEnd_472354 < baseStart_472354 := by decide
  rcases family_descends (prefixWord ++ tailWord_472354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472355 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_472355 : Nat := 118140960795 + 472355 * 2 ^ 59
def prefixEnd_472355 : Nat := 4983230072969 + 3 ^ 40 * 472355 * 2
def baseEnd_472355 : Nat := 215595692937426348969053

theorem tailTrace_472355 : CollatzResearch.WordTrace tailWord_472355 prefixEnd_472355 215595692937426348969053 := by
  unfold tailWord_472355
  simp only [CollatzResearch.WordTrace]
  refine ⟨17228202203745981656498519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11485468135830654437665679 17228202203745981656498519)
  ·
    refine ⟨25842303305618972484747779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17228202203745981656498519 25842303305618972484747779)
    ·
      refine ⟨38763454958428458727121669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25842303305618972484747779 38763454958428458727121669)
      ·
        refine ⟨7268147804705336011335313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38763454958428458727121669 7268147804705336011335313)
        ·
          refine ⟨5451110853529002008501485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7268147804705336011335313 5451110853529002008501485)
          ·
            refine ⟨2044166570073375753188057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5451110853529002008501485 2044166570073375753188057)
            ·
              refine ⟨1533124927555031814891043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044166570073375753188057 1533124927555031814891043)
              ·
                refine ⟨2299687391332547722336565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533124927555031814891043 2299687391332547722336565)
                ·
                  refine ⟨215595692937426348969053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2299687391332547722336565 215595692937426348969053)
                  ·
                    rfl

theorem cell20_472355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_472355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472355 prefixEnd_472355 := by exact prefixLift 472355
  have htrace : WordTrace (prefixWord ++ tailWord_472355) baseStart_472355 baseEnd_472355 := by
    simpa [prefixWord, tailWord_472355, baseEnd_472355] using wordTrace_append hprefix tailTrace_472355
  have hstable : (prefixWord ++ tailWord_472355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472355).length < 2 ^ (prefixWord ++ tailWord_472355).sum := by decide
  have hdescent : baseEnd_472355 < baseStart_472355 := by decide
  rcases family_descends (prefixWord ++ tailWord_472355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472365 : List Nat := [1, 5, 3, 1, 1, 1, 1, 7]
def baseStart_472365 : Nat := 118140960795 + 472365 * 2 ^ 59
def prefixEnd_472365 : Nat := 4983230072969 + 3 ^ 40 * 472365 * 2
def baseEnd_472365 : Nat := 71866752403303586211893

theorem tailTrace_472365 : CollatzResearch.WordTrace tailWord_472365 prefixEnd_472365 71866752403303586211893 := by
  unfold tailWord_472365
  simp only [CollatzResearch.WordTrace]
  refine ⟨17228566933709753364362549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11485711289139835576241699 17228566933709753364362549)
  ·
    refine ⟨1615178150035289377908989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17228566933709753364362549 1615178150035289377908989)
    ·
      refine ⟨605691806263233516715871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1615178150035289377908989 605691806263233516715871)
      ·
        refine ⟨908537709394850275073807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605691806263233516715871 908537709394850275073807)
        ·
          refine ⟨1362806564092275412610711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908537709394850275073807 1362806564092275412610711)
          ·
            refine ⟨2044209846138413118916067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362806564092275412610711 2044209846138413118916067)
            ·
              refine ⟨3066314769207619678374101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044209846138413118916067 3066314769207619678374101)
              ·
                refine ⟨71866752403303586211893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3066314769207619678374101 71866752403303586211893)
                ·
                  rfl

theorem cell20_472365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_472365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472365 prefixEnd_472365 := by exact prefixLift 472365
  have htrace : WordTrace (prefixWord ++ tailWord_472365) baseStart_472365 baseEnd_472365 := by
    simpa [prefixWord, tailWord_472365, baseEnd_472365] using wordTrace_append hprefix tailTrace_472365
  have hstable : (prefixWord ++ tailWord_472365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472365).length < 2 ^ (prefixWord ++ tailWord_472365).sum := by decide
  have hdescent : baseEnd_472365 < baseStart_472365 := by decide
  rcases family_descends (prefixWord ++ tailWord_472365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472407 : List Nat := [1, 1, 3, 2, 3, 10]
def baseStart_472407 : Nat := 118140960795 + 472407 * 2 ^ 59
def prefixEnd_472407 : Nat := 4983230072969 + 3 ^ 40 * 472407 * 2
def baseEnd_472407 : Nat := 7985904709420195527241

theorem tailTrace_472407 : CollatzResearch.WordTrace tailWord_472407 prefixEnd_472407 7985904709420195527241 := by
  unfold tailWord_472407
  simp only [CollatzResearch.WordTrace]
  refine ⟨17230098799557594537391475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11486732533038396358260983 17230098799557594537391475)
  ·
    refine ⟨25845148199336391806087213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17230098799557594537391475 25845148199336391806087213)
    ·
      refine ⟨9691930574751146927282705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25845148199336391806087213 9691930574751146927282705)
      ·
        refine ⟨7268947931063360195462029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9691930574751146927282705 7268947931063360195462029)
        ·
          refine ⟨2725855474148760073298261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7268947931063360195462029 2725855474148760073298261)
          ·
            refine ⟨7985904709420195527241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2725855474148760073298261 7985904709420195527241)
            ·
              rfl

theorem cell20_472407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 10].length) (baseStart_472407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472407 prefixEnd_472407 := by exact prefixLift 472407
  have htrace : WordTrace (prefixWord ++ tailWord_472407) baseStart_472407 baseEnd_472407 := by
    simpa [prefixWord, tailWord_472407, baseEnd_472407] using wordTrace_append hprefix tailTrace_472407
  have hstable : (prefixWord ++ tailWord_472407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472407).length < 2 ^ (prefixWord ++ tailWord_472407).sum := by decide
  have hdescent : baseEnd_472407 < baseStart_472407 := by decide
  rcases family_descends (prefixWord ++ tailWord_472407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472431 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_472431 : Nat := 118140960795 + 472431 * 2 ^ 59
def prefixEnd_472431 : Nat := 4983230072969 + 3 ^ 40 * 472431 * 2
def baseEnd_472431 : Nat := 215630381408307862435409

theorem tailTrace_472431 : CollatzResearch.WordTrace tailWord_472431 prefixEnd_472431 215630381408307862435409 := by
  unfold tailWord_472431
  simp only [CollatzResearch.WordTrace]
  refine ⟨17230974151470646636265147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11487316100980431090843431 17230974151470646636265147)
  ·
    refine ⟨25846461227205969954397721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17230974151470646636265147 25846461227205969954397721)
    ·
      refine ⟨19384845920404477465798291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25846461227205969954397721 19384845920404477465798291)
      ·
        refine ⟨29077268880606716198697437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19384845920404477465798291 29077268880606716198697437)
        ·
          refine ⟨10903975830227518574511539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29077268880606716198697437 10903975830227518574511539)
          ·
            refine ⟨16355963745341277861767309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10903975830227518574511539 16355963745341277861767309)
            ·
              refine ⟨6133486404502979198162741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16355963745341277861767309 6133486404502979198162741)
              ·
                refine ⟨575014350422154299827757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6133486404502979198162741 575014350422154299827757)
                ·
                  refine ⟨215630381408307862435409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575014350422154299827757 215630381408307862435409)
                  ·
                    rfl

theorem cell20_472431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_472431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472431 prefixEnd_472431 := by exact prefixLift 472431
  have htrace : WordTrace (prefixWord ++ tailWord_472431) baseStart_472431 baseEnd_472431 := by
    simpa [prefixWord, tailWord_472431, baseEnd_472431] using wordTrace_append hprefix tailTrace_472431
  have hstable : (prefixWord ++ tailWord_472431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472431).length < 2 ^ (prefixWord ++ tailWord_472431).sum := by decide
  have hdescent : baseEnd_472431 < baseStart_472431 := by decide
  rcases family_descends (prefixWord ++ tailWord_472431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472472 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_472472 : Nat := 118140960795 + 472472 * 2 ^ 59
def prefixEnd_472472 : Nat := 4983230072969 + 3 ^ 40 * 472472 * 2
def baseEnd_472472 : Nat := 215649094925493942068575

theorem tailTrace_472472 : CollatzResearch.WordTrace tailWord_472472 prefixEnd_472472 215649094925493942068575 := by
  unfold tailWord_472472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616234772161055319253835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11488313029548073759005113 8616234772161055319253835)
  ·
    refine ⟨12924352158241582978880753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8616234772161055319253835 12924352158241582978880753)
    ·
      refine ⟨9693264118681187234160565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12924352158241582978880753 9693264118681187234160565)
      ·
        refine ⟨908743511126361303202553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9693264118681187234160565 908743511126361303202553)
        ·
          refine ⟨681557633344770977401915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908743511126361303202553 681557633344770977401915)
          ·
            refine ⟨1022336450017156466102873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681557633344770977401915 1022336450017156466102873)
            ·
              refine ⟨766752337512867349577155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022336450017156466102873 766752337512867349577155)
              ·
                refine ⟨1150128506269301024365733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766752337512867349577155 1150128506269301024365733)
                ·
                  refine ⟨215649094925493942068575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150128506269301024365733 215649094925493942068575)
                  ·
                    rfl

theorem cell20_472472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_472472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472472 prefixEnd_472472 := by exact prefixLift 472472
  have htrace : WordTrace (prefixWord ++ tailWord_472472) baseStart_472472 baseEnd_472472 := by
    simpa [prefixWord, tailWord_472472, baseEnd_472472] using wordTrace_append hprefix tailTrace_472472
  have hstable : (prefixWord ++ tailWord_472472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472472).length < 2 ^ (prefixWord ++ tailWord_472472).sum := by decide
  have hdescent : baseEnd_472472 < baseStart_472472 := by decide
  rcases family_descends (prefixWord ++ tailWord_472472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472483 : List Nat := [1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_472483 : Nat := 118140960795 + 472483 * 2 ^ 59
def prefixEnd_472483 : Nat := 4983230072969 + 3 ^ 40 * 472483 * 2
def baseEnd_472483 : Nat := 71884705208408930900621

theorem tailTrace_472483 : CollatzResearch.WordTrace tailWord_472483 prefixEnd_472483 71884705208408930900621 := by
  unfold tailWord_472483
  simp only [CollatzResearch.WordTrace]
  refine ⟨17232870747282259517158103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11488580498188173011438735 17232870747282259517158103)
  ·
    refine ⟨25849306120923389275737155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17232870747282259517158103 25849306120923389275737155)
    ·
      refine ⟨38773959181385083913605733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25849306120923389275737155 38773959181385083913605733)
      ·
        refine ⟨7270117346509703233801075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38773959181385083913605733 7270117346509703233801075)
        ·
          refine ⟨10905176019764554850701613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7270117346509703233801075 10905176019764554850701613)
          ·
            refine ⟨4089441007411708069013105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10905176019764554850701613 4089441007411708069013105)
            ·
              refine ⟨3067080755558781051759829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089441007411708069013105 3067080755558781051759829)
              ·
                refine ⟨71884705208408930900621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3067080755558781051759829 71884705208408930900621)
                ·
                  rfl

theorem cell20_472483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_472483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472483 prefixEnd_472483 := by exact prefixLift 472483
  have htrace : WordTrace (prefixWord ++ tailWord_472483) baseStart_472483 baseEnd_472483 := by
    simpa [prefixWord, tailWord_472483, baseEnd_472483] using wordTrace_append hprefix tailTrace_472483
  have hstable : (prefixWord ++ tailWord_472483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472483).length < 2 ^ (prefixWord ++ tailWord_472483).sum := by decide
  have hdescent : baseEnd_472483 < baseStart_472483 := by decide
  rcases family_descends (prefixWord ++ tailWord_472483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472538 : List Nat := [3, 1, 1, 2, 3, 3, 2, 5]
def baseStart_472538 : Nat := 118140960795 + 472538 * 2 ^ 59
def prefixEnd_472538 : Nat := 4983230072969 + 3 ^ 40 * 472538 * 2
def baseEnd_472538 : Nat := 71893073041297015289435

theorem tailTrace_472538 : CollatzResearch.WordTrace tailWord_472538 prefixEnd_472538 71893073041297015289435 := by
  unfold tailWord_472538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308719190520750977602567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11489917841388669273606845 4308719190520750977602567)
  ·
    refine ⟨6463078785781126466403851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4308719190520750977602567 6463078785781126466403851)
    ·
      refine ⟨9694618178671689699605777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6463078785781126466403851 9694618178671689699605777)
      ·
        refine ⟨7270963634003767274704333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9694618178671689699605777 7270963634003767274704333)
        ·
          refine ⟨2726611362751412728014125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7270963634003767274704333 2726611362751412728014125)
          ·
            refine ⟨1022479261031779773005297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2726611362751412728014125 1022479261031779773005297)
            ·
              refine ⟨766859445773834829753973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022479261031779773005297 766859445773834829753973)
              ·
                refine ⟨71893073041297015289435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 766859445773834829753973 71893073041297015289435)
                ·
                  rfl

theorem cell20_472538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_472538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472538 prefixEnd_472538 := by exact prefixLift 472538
  have htrace : WordTrace (prefixWord ++ tailWord_472538) baseStart_472538 baseEnd_472538 := by
    simpa [prefixWord, tailWord_472538, baseEnd_472538] using wordTrace_append hprefix tailTrace_472538
  have hstable : (prefixWord ++ tailWord_472538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472538).length < 2 ^ (prefixWord ++ tailWord_472538).sum := by decide
  have hdescent : baseEnd_472538 < baseStart_472538 := by decide
  rcases family_descends (prefixWord ++ tailWord_472538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472541 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 3]
def baseStart_472541 : Nat := 118140960795 + 472541 * 2 ^ 59
def prefixEnd_472541 : Nat := 4983230072969 + 3 ^ 40 * 472541 * 2
def baseEnd_472541 : Nat := 215680588405636368768293

theorem tailTrace_472541 : CollatzResearch.WordTrace tailWord_472541 prefixEnd_472541 215680588405636368768293 := by
  unfold tailWord_472541
  simp only [CollatzResearch.WordTrace]
  refine ⟨17234986181072135422769477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11489990787381423615179651 17234986181072135422769477)
  ·
    refine ⟨3231559908951025391769277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17234986181072135422769477 3231559908951025391769277)
    ·
      refine ⟨1211834965856634521913479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3231559908951025391769277 1211834965856634521913479)
      ·
        refine ⟨1817752448784951782870219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211834965856634521913479 1817752448784951782870219)
        ·
          refine ⟨2726628673177427674305329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817752448784951782870219 2726628673177427674305329)
          ·
            refine ⟨2044971504883070755728997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2726628673177427674305329 2044971504883070755728997)
            ·
              refine ⟨383432157165575766699187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2044971504883070755728997 383432157165575766699187)
              ·
                refine ⟨575148235748363650048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383432157165575766699187 575148235748363650048781)
                ·
                  refine ⟨215680588405636368768293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575148235748363650048781 215680588405636368768293)
                  ·
                    rfl

theorem cell20_472541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_472541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472541 prefixEnd_472541 := by exact prefixLift 472541
  have htrace : WordTrace (prefixWord ++ tailWord_472541) baseStart_472541 baseEnd_472541 := by
    simpa [prefixWord, tailWord_472541, baseEnd_472541] using wordTrace_append hprefix tailTrace_472541
  have hstable : (prefixWord ++ tailWord_472541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472541).length < 2 ^ (prefixWord ++ tailWord_472541).sum := by decide
  have hdescent : baseEnd_472541 < baseStart_472541 := by decide
  rcases family_descends (prefixWord ++ tailWord_472541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472552 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_472552 : Nat := 118140960795 + 472552 * 2 ^ 59
def prefixEnd_472552 : Nat := 4983230072969 + 3 ^ 40 * 472552 * 2
def baseEnd_472552 : Nat := 215685609105369219401581

theorem tailTrace_472552 : CollatzResearch.WordTrace tailWord_472552 prefixEnd_472552 215685609105369219401581 := by
  unfold tailWord_472552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8617693692016142150709955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11490258256021522867613273 8617693692016142150709955)
  ·
    refine ⟨12926540538024213226064933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8617693692016142150709955 12926540538024213226064933)
    ·
      refine ⟨2423726350879539979887175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12926540538024213226064933 2423726350879539979887175)
      ·
        refine ⟨3635589526319309969830763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423726350879539979887175 3635589526319309969830763)
        ·
          refine ⟨5453384289478964954746145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3635589526319309969830763 5453384289478964954746145)
          ·
            refine ⟨4090038217109223716059609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5453384289478964954746145 4090038217109223716059609)
            ·
              refine ⟨3067528662831917787044707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090038217109223716059609 3067528662831917787044707)
              ·
                refine ⟨4601292994247876680567061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067528662831917787044707 4601292994247876680567061)
                ·
                  refine ⟨215685609105369219401581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4601292994247876680567061 215685609105369219401581)
                  ·
                    rfl

theorem cell20_472552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_472552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472552 prefixEnd_472552 := by exact prefixLift 472552
  have htrace : WordTrace (prefixWord ++ tailWord_472552) baseStart_472552 baseEnd_472552 := by
    simpa [prefixWord, tailWord_472552, baseEnd_472552] using wordTrace_append hprefix tailTrace_472552
  have hstable : (prefixWord ++ tailWord_472552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472552).length < 2 ^ (prefixWord ++ tailWord_472552).sum := by decide
  have hdescent : baseEnd_472552 < baseStart_472552 := by decide
  rcases family_descends (prefixWord ++ tailWord_472552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472559 : List Nat := [1, 1, 2, 1, 4, 1, 4, 6]
def baseStart_472559 : Nat := 118140960795 + 472559 * 2 ^ 59
def prefixEnd_472559 : Nat := 4983230072969 + 3 ^ 40 * 472559 * 2
def baseEnd_472559 : Nat := 71896268032036102056073

theorem tailTrace_472559 : CollatzResearch.WordTrace tailWord_472559 prefixEnd_472559 71896268032036102056073 := by
  unfold tailWord_472559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17235642695006924496924731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11490428463337949664616487 17235642695006924496924731)
  ·
    refine ⟨25853464042510386745387097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17235642695006924496924731 25853464042510386745387097)
    ·
      refine ⟨19390098031882790059040323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25853464042510386745387097 19390098031882790059040323)
      ·
        refine ⟨29085147047824185088560485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19390098031882790059040323 29085147047824185088560485)
        ·
          refine ⟨5453465071467034704105091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29085147047824185088560485 5453465071467034704105091)
          ·
            refine ⟨8180197607200552056157637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453465071467034704105091 8180197607200552056157637)
            ·
              refine ⟨1533787051350103510529557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8180197607200552056157637 1533787051350103510529557)
              ·
                refine ⟨71896268032036102056073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1533787051350103510529557 71896268032036102056073)
                ·
                  rfl

theorem cell20_472559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_472559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472559 prefixEnd_472559 := by exact prefixLift 472559
  have htrace : WordTrace (prefixWord ++ tailWord_472559) baseStart_472559 baseEnd_472559 := by
    simpa [prefixWord, tailWord_472559, baseEnd_472559] using wordTrace_append hprefix tailTrace_472559
  have hstable : (prefixWord ++ tailWord_472559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472559).length < 2 ^ (prefixWord ++ tailWord_472559).sum := by decide
  have hdescent : baseEnd_472559 < baseStart_472559 := by decide
  rcases family_descends (prefixWord ++ tailWord_472559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472569 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 2]
def baseStart_472569 : Nat := 118140960795 + 472569 * 2 ^ 59
def prefixEnd_472569 : Nat := 4983230072969 + 3 ^ 40 * 472569 * 2
def baseEnd_472569 : Nat := 215693368368592715834845

theorem tailTrace_472569 : CollatzResearch.WordTrace tailWord_472569 prefixEnd_472569 215693368368592715834845 := by
  unfold tailWord_472569
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236007424970696204788761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11490671616647130803192507 17236007424970696204788761)
  ·
    refine ⟨12927005568728022153591571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17236007424970696204788761 12927005568728022153591571)
    ·
      refine ⟨19390508353092033230387357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12927005568728022153591571 19390508353092033230387357)
      ·
        refine ⟨7271440632409512461395259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19390508353092033230387357 7271440632409512461395259)
        ·
          refine ⟨10907160948614268692092889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271440632409512461395259 10907160948614268692092889)
          ·
            refine ⟨8180370711460701519069667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10907160948614268692092889 8180370711460701519069667)
            ·
              refine ⟨12270556067191052278604501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180370711460701519069667 12270556067191052278604501)
              ·
                refine ⟨287591157824790287779793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12270556067191052278604501 287591157824790287779793)
                ·
                  refine ⟨215693368368592715834845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287591157824790287779793 215693368368592715834845)
                  ·
                    rfl

theorem cell20_472569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_472569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472569 prefixEnd_472569 := by exact prefixLift 472569
  have htrace : WordTrace (prefixWord ++ tailWord_472569) baseStart_472569 baseEnd_472569 := by
    simpa [prefixWord, tailWord_472569, baseEnd_472569] using wordTrace_append hprefix tailTrace_472569
  have hstable : (prefixWord ++ tailWord_472569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472569).length < 2 ^ (prefixWord ++ tailWord_472569).sum := by decide
  have hdescent : baseEnd_472569 < baseStart_472569 := by decide
  rcases family_descends (prefixWord ++ tailWord_472569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472586 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_472586 : Nat := 118140960795 + 472586 * 2 ^ 59
def prefixEnd_472586 : Nat := 4983230072969 + 3 ^ 40 * 472586 * 2
def baseEnd_472586 : Nat := 215701127631816212268109

theorem tailTrace_472586 : CollatzResearch.WordTrace tailWord_472586 prefixEnd_472586 215701127631816212268109 := by
  unfold tailWord_472586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309156866477277027039403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11491084977272738738771741 4309156866477277027039403)
  ·
    refine ⟨6463735299715915540559105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4309156866477277027039403 6463735299715915540559105)
    ·
      refine ⟨4847801474786936655419329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6463735299715915540559105 4847801474786936655419329)
      ·
        refine ⟨3635851106090202491564497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4847801474786936655419329 3635851106090202491564497)
        ·
          refine ⟨2726888329567651868673373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3635851106090202491564497 2726888329567651868673373)
          ·
            refine ⟨1022583123587869450752515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2726888329567651868673373 1022583123587869450752515)
            ·
              refine ⟨1533874685381804176128773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022583123587869450752515 1533874685381804176128773)
              ·
                refine ⟨287601503509088283024145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1533874685381804176128773 287601503509088283024145)
                ·
                  refine ⟨215701127631816212268109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287601503509088283024145 215701127631816212268109)
                  ·
                    rfl

theorem cell20_472586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_472586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472586 prefixEnd_472586 := by exact prefixLift 472586
  have htrace : WordTrace (prefixWord ++ tailWord_472586) baseStart_472586 baseEnd_472586 := by
    simpa [prefixWord, tailWord_472586, baseEnd_472586] using wordTrace_append hprefix tailTrace_472586
  have hstable : (prefixWord ++ tailWord_472586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472586).length < 2 ^ (prefixWord ++ tailWord_472586).sum := by decide
  have hdescent : baseEnd_472586 < baseStart_472586 := by decide
  rcases family_descends (prefixWord ++ tailWord_472586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472589 : List Nat := [1, 7, 1, 1, 2, 2, 1, 5]
def baseStart_472589 : Nat := 118140960795 + 472589 * 2 ^ 59
def prefixEnd_472589 : Nat := 4983230072969 + 3 ^ 40 * 472589 * 2
def baseEnd_472589 : Nat := 71900832304520511722699

theorem tailTrace_472589 : CollatzResearch.WordTrace tailWord_472589 prefixEnd_472589 71900832304520511722699 := by
  unfold tailWord_472589
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236736884898239620516821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11491157923265493080344547 17236736884898239620516821)
  ·
    refine ⟨403986020739802491105863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17236736884898239620516821 403986020739802491105863)
    ·
      refine ⟨605979031109703736658795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403986020739802491105863 605979031109703736658795)
      ·
        refine ⟨908968546664555604988193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605979031109703736658795 908968546664555604988193)
        ·
          refine ⟨681726409998416703741145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908968546664555604988193 681726409998416703741145)
          ·
            refine ⟨511294807498812527805859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681726409998416703741145 511294807498812527805859)
            ·
              refine ⟨766942211248218791708789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511294807498812527805859 766942211248218791708789)
              ·
                refine ⟨71900832304520511722699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 766942211248218791708789 71900832304520511722699)
                ·
                  rfl

theorem cell20_472589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_472589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472589 prefixEnd_472589 := by exact prefixLift 472589
  have htrace : WordTrace (prefixWord ++ tailWord_472589) baseStart_472589 baseEnd_472589 := by
    simpa [prefixWord, tailWord_472589, baseEnd_472589] using wordTrace_append hprefix tailTrace_472589
  have hstable : (prefixWord ++ tailWord_472589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472589).length < 2 ^ (prefixWord ++ tailWord_472589).sum := by decide
  have hdescent : baseEnd_472589 < baseStart_472589 := by decide
  rcases family_descends (prefixWord ++ tailWord_472589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472606 : List Nat := [4, 3, 3, 1, 1, 1, 3, 4]
def baseStart_472606 : Nat := 118140960795 + 472606 * 2 ^ 59
def prefixEnd_472606 : Nat := 4983230072969 + 3 ^ 40 * 472606 * 2
def baseEnd_472606 : Nat := 71903418725595010533787

theorem tailTrace_472606 : CollatzResearch.WordTrace tailWord_472606 prefixEnd_472606 71903418725595010533787 := by
  unfold tailWord_472606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154669615729581440485709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11491571283891101015923781 2154669615729581440485709)
  ·
    refine ⟨808001105898593040182141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2154669615729581440485709 808001105898593040182141)
    ·
      refine ⟨303000414711972390068303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 808001105898593040182141 303000414711972390068303)
      ·
        refine ⟨454500622067958585102455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303000414711972390068303 454500622067958585102455)
        ·
          refine ⟨681750933101937877653683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454500622067958585102455 681750933101937877653683)
          ·
            refine ⟨1022626399652906816480525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681750933101937877653683 1022626399652906816480525)
            ·
              refine ⟨383484899869840056180197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1022626399652906816480525 383484899869840056180197)
              ·
                refine ⟨71903418725595010533787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383484899869840056180197 71903418725595010533787)
                ·
                  rfl

theorem cell20_472606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_472606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472606 prefixEnd_472606 := by exact prefixLift 472606
  have htrace : WordTrace (prefixWord ++ tailWord_472606) baseStart_472606 baseEnd_472606 := by
    simpa [prefixWord, tailWord_472606, baseEnd_472606] using wordTrace_append hprefix tailTrace_472606
  have hstable : (prefixWord ++ tailWord_472606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472606).length < 2 ^ (prefixWord ++ tailWord_472606).sum := by decide
  have hdescent : baseEnd_472606 < baseStart_472606 := by decide
  rcases family_descends (prefixWord ++ tailWord_472606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472645 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 2]
def baseStart_472645 : Nat := 118140960795 + 472645 * 2 ^ 59
def prefixEnd_472645 : Nat := 4983230072969 + 3 ^ 40 * 472645 * 2
def baseEnd_472645 : Nat := 215728056839474229301201

theorem tailTrace_472645 : CollatzResearch.WordTrace tailWord_472645 prefixEnd_472645 215728056839474229301201 := by
  unfold tailWord_472645
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238779372695361184555389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11492519581796907456370259 17238779372695361184555389)
  ·
    refine ⟨6464542264760760444208271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17238779372695361184555389 6464542264760760444208271)
    ·
      refine ⟨9696813397141140666312407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464542264760760444208271 9696813397141140666312407)
      ·
        refine ⟨14545220095711710999468611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9696813397141140666312407 14545220095711710999468611)
        ·
          refine ⟨21817830143567566499202917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14545220095711710999468611 21817830143567566499202917)
          ·
            refine ⟨4090843151918918718600547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21817830143567566499202917 4090843151918918718600547)
            ·
              refine ⟨6136264727878378077900821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090843151918918718600547 6136264727878378077900821)
              ·
                refine ⟨287637409119298972401601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6136264727878378077900821 287637409119298972401601)
                ·
                  refine ⟨215728056839474229301201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287637409119298972401601 215728056839474229301201)
                  ·
                    rfl

theorem cell20_472645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_472645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472645 prefixEnd_472645 := by exact prefixLift 472645
  have htrace : WordTrace (prefixWord ++ tailWord_472645) baseStart_472645 baseEnd_472645 := by
    simpa [prefixWord, tailWord_472645, baseEnd_472645] using wordTrace_append hprefix tailTrace_472645
  have hstable : (prefixWord ++ tailWord_472645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472645).length < 2 ^ (prefixWord ++ tailWord_472645).sum := by decide
  have hdescent : baseEnd_472645 < baseStart_472645 := by decide
  rcases family_descends (prefixWord ++ tailWord_472645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472673 : List Nat := [1, 2, 3, 1, 1, 3, 3, 6]
def baseStart_472673 : Nat := 118140960795 + 472673 * 2 ^ 59
def prefixEnd_472673 : Nat := 4983230072969 + 3 ^ 40 * 472673 * 2
def baseEnd_472673 : Nat := 71913612267476858789251

theorem tailTrace_472673 : CollatzResearch.WordTrace tailWord_472673 prefixEnd_472673 71913612267476858789251 := by
  unfold tailWord_472673
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239800616593921966574673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11493200411062614644383115 17239800616593921966574673)
  ·
    refine ⟨12929850462445441474931005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17239800616593921966574673 12929850462445441474931005)
    ·
      refine ⟨4848693923417040553099127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12929850462445441474931005 4848693923417040553099127)
      ·
        refine ⟨7273040885125560829648691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4848693923417040553099127 7273040885125560829648691)
        ·
          refine ⟨10909561327688341244473037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7273040885125560829648691 10909561327688341244473037)
          ·
            refine ⟨4091085497883127966677389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10909561327688341244473037 4091085497883127966677389)
            ·
              refine ⟨1534157061706172987504021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4091085497883127966677389 1534157061706172987504021)
              ·
                refine ⟨71913612267476858789251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1534157061706172987504021 71913612267476858789251)
                ·
                  rfl

theorem cell20_472673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_472673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472673 prefixEnd_472673 := by exact prefixLift 472673
  have htrace : WordTrace (prefixWord ++ tailWord_472673) baseStart_472673 baseEnd_472673 := by
    simpa [prefixWord, tailWord_472673, baseEnd_472673] using wordTrace_append hprefix tailTrace_472673
  have hstable : (prefixWord ++ tailWord_472673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472673).length < 2 ^ (prefixWord ++ tailWord_472673).sum := by decide
  have hdescent : baseEnd_472673 < baseStart_472673 := by decide
  rcases family_descends (prefixWord ++ tailWord_472673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472690 : List Nat := [3, 2, 1, 2, 3, 3, 6]
def baseStart_472690 : Nat := 118140960795 + 472690 * 2 ^ 59
def prefixEnd_472690 : Nat := 4983230072969 + 3 ^ 40 * 472690 * 2
def baseEnd_472690 : Nat := 23972066229517119200113

theorem tailTrace_472690 : CollatzResearch.WordTrace tailWord_472690 prefixEnd_472690 23972066229517119200113 := by
  unfold tailWord_472690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310105164383083467485881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11493613771688222579962349 4310105164383083467485881)
  ·
    refine ⟨3232578873287312600614411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4310105164383083467485881 3232578873287312600614411)
    ·
      refine ⟨4848868309930968900921617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232578873287312600614411 4848868309930968900921617)
      ·
        refine ⟨3636651232448226675691213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4848868309930968900921617 3636651232448226675691213)
        ·
          refine ⟨1363744212168085003384205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3636651232448226675691213 1363744212168085003384205)
          ·
            refine ⟨511404079563031876269077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1363744212168085003384205 511404079563031876269077)
            ·
              refine ⟨23972066229517119200113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 511404079563031876269077 23972066229517119200113)
              ·
                rfl

theorem cell20_472690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 6].length) (baseStart_472690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472690 prefixEnd_472690 := by exact prefixLift 472690
  have htrace : WordTrace (prefixWord ++ tailWord_472690) baseStart_472690 baseEnd_472690 := by
    simpa [prefixWord, tailWord_472690, baseEnd_472690] using wordTrace_append hprefix tailTrace_472690
  have hstable : (prefixWord ++ tailWord_472690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472690).length < 2 ^ (prefixWord ++ tailWord_472690).sum := by decide
  have hdescent : baseEnd_472690 < baseStart_472690 := by decide
  rcases family_descends (prefixWord ++ tailWord_472690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472697 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_472697 : Nat := 118140960795 + 472697 * 2 ^ 59
def prefixEnd_472697 : Nat := 4983230072969 + 3 ^ 40 * 472697 * 2
def baseEnd_472697 : Nat := 215751791056393159567655

theorem tailTrace_472697 : CollatzResearch.WordTrace tailWord_472697 prefixEnd_472697 215751791056393159567655 := by
  unfold tailWord_472697
  simp only [CollatzResearch.WordTrace]
  refine ⟨17240675968506974065448345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11493783979004649376965563 17240675968506974065448345)
  ·
    refine ⟨12930506976380230549086259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17240675968506974065448345 12930506976380230549086259)
    ·
      refine ⟨19395760464570345823629389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12930506976380230549086259 19395760464570345823629389)
      ·
        refine ⟨7273410174213879683861021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19395760464570345823629389 7273410174213879683861021)
        ·
          refine ⟨2727528815330204881447883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7273410174213879683861021 2727528815330204881447883)
          ·
            refine ⟨4091293222995307322171825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727528815330204881447883 4091293222995307322171825)
            ·
              refine ⟨3068469917246480491628869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091293222995307322171825 3068469917246480491628869)
              ·
                refine ⟨575338109483715092180413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3068469917246480491628869 575338109483715092180413)
                ·
                  refine ⟨215751791056393159567655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575338109483715092180413 215751791056393159567655)
                  ·
                    rfl

theorem cell20_472697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_472697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472697 prefixEnd_472697 := by exact prefixLift 472697
  have htrace : WordTrace (prefixWord ++ tailWord_472697) baseStart_472697 baseEnd_472697 := by
    simpa [prefixWord, tailWord_472697, baseEnd_472697] using wordTrace_append hprefix tailTrace_472697
  have hstable : (prefixWord ++ tailWord_472697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472697).length < 2 ^ (prefixWord ++ tailWord_472697).sum := by decide
  have hdescent : baseEnd_472697 < baseStart_472697 := by decide
  rcases family_descends (prefixWord ++ tailWord_472697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472711 : List Nat := [1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_472711 : Nat := 118140960795 + 472711 * 2 ^ 59
def prefixEnd_472711 : Nat := 4983230072969 + 3 ^ 40 * 472711 * 2
def baseEnd_472711 : Nat := 71919393679290444366977

theorem tailTrace_472711 : CollatzResearch.WordTrace tailWord_472711 prefixEnd_472711 71919393679290444366977 := by
  unfold tailWord_472711
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241186590456254456457987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11494124393637502970971991 17241186590456254456457987)
  ·
    refine ⟨25861779885684381684686981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17241186590456254456457987 25861779885684381684686981)
    ·
      refine ⟨4849083728565821565878809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25861779885684381684686981 4849083728565821565878809)
      ·
        refine ⟨3636812796424366174409107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4849083728565821565878809 3636812796424366174409107)
        ·
          refine ⟨5455219194636549261613661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636812796424366174409107 5455219194636549261613661)
          ·
            refine ⟨2045707197988705973105123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5455219194636549261613661 2045707197988705973105123)
            ·
              refine ⟨3068560796983058959657685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045707197988705973105123 3068560796983058959657685)
              ·
                refine ⟨71919393679290444366977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3068560796983058959657685 71919393679290444366977)
                ·
                  rfl

theorem cell20_472711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_472711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472711 prefixEnd_472711 := by exact prefixLift 472711
  have htrace : WordTrace (prefixWord ++ tailWord_472711) baseStart_472711 baseEnd_472711 := by
    simpa [prefixWord, tailWord_472711, baseEnd_472711] using wordTrace_append hprefix tailTrace_472711
  have hstable : (prefixWord ++ tailWord_472711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472711).length < 2 ^ (prefixWord ++ tailWord_472711).sum := by decide
  have hdescent : baseEnd_472711 < baseStart_472711 := by decide
  rcases family_descends (prefixWord ++ tailWord_472711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472714 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_472714 : Nat := 118140960795 + 472714 * 2 ^ 59
def prefixEnd_472714 : Nat := 4983230072969 + 3 ^ 40 * 472714 * 2
def baseEnd_472714 : Nat := 215759550319616656000919

theorem tailTrace_472714 : CollatzResearch.WordTrace tailWord_472714 prefixEnd_472714 215759550319616656000919 := by
  unfold tailWord_472714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310324002361346492204299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11494197339630257312544797 4310324002361346492204299)
  ·
    refine ⟨6465486003542019738306449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4310324002361346492204299 6465486003542019738306449)
    ·
      refine ⟨4849114502656514803729837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6465486003542019738306449 4849114502656514803729837)
      ·
        refine ⟨1818417938496193051398689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4849114502656514803729837 1818417938496193051398689)
        ·
          refine ⟨1363813453872144788549017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818417938496193051398689 1363813453872144788549017)
          ·
            refine ⟨1022860090404108591411763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363813453872144788549017 1022860090404108591411763)
            ·
              refine ⟨1534290135606162887117645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022860090404108591411763 1534290135606162887117645)
              ·
                refine ⟨575358800852311082669117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1534290135606162887117645 575358800852311082669117)
                ·
                  refine ⟨215759550319616656000919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575358800852311082669117 215759550319616656000919)
                  ·
                    rfl

theorem cell20_472714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_472714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472714 prefixEnd_472714 := by exact prefixLift 472714
  have htrace : WordTrace (prefixWord ++ tailWord_472714) baseStart_472714 baseEnd_472714 := by
    simpa [prefixWord, tailWord_472714, baseEnd_472714] using wordTrace_append hprefix tailTrace_472714
  have hstable : (prefixWord ++ tailWord_472714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472714).length < 2 ^ (prefixWord ++ tailWord_472714).sum := by decide
  have hdescent : baseEnd_472714 < baseStart_472714 := by decide
  rcases family_descends (prefixWord ++ tailWord_472714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472763 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_472763 : Nat := 118140960795 + 472763 * 2 ^ 59
def prefixEnd_472763 : Nat := 4983230072969 + 3 ^ 40 * 472763 * 2
def baseEnd_472763 : Nat := 215781915254790263367385

theorem tailTrace_472763 : CollatzResearch.WordTrace tailWord_472763 prefixEnd_472763 215781915254790263367385 := by
  unfold tailWord_472763
  simp only [CollatzResearch.WordTrace]
  refine ⟨17243083186267867337350943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11495388790845244891567295 17243083186267867337350943)
  ·
    refine ⟨25864624779401801006026415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17243083186267867337350943 25864624779401801006026415)
    ·
      refine ⟨38796937169102701509039623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864624779401801006026415 38796937169102701509039623)
      ·
        refine ⟨58195405753654052263559435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38796937169102701509039623 58195405753654052263559435)
        ·
          refine ⟨87293108630481078395339153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58195405753654052263559435 87293108630481078395339153)
          ·
            refine ⟨65469831472860808796504365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87293108630481078395339153 65469831472860808796504365)
            ·
              refine ⟨24551186802322803298689137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65469831472860808796504365 24551186802322803298689137)
              ·
                refine ⟨18413390101742102474016853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24551186802322803298689137 18413390101742102474016853)
                ·
                  refine ⟨215781915254790263367385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18413390101742102474016853 215781915254790263367385)
                  ·
                    rfl

theorem cell20_472763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_472763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472763 prefixEnd_472763 := by exact prefixLift 472763
  have htrace : WordTrace (prefixWord ++ tailWord_472763) baseStart_472763 baseEnd_472763 := by
    simpa [prefixWord, tailWord_472763, baseEnd_472763] using wordTrace_append hprefix tailTrace_472763
  have hstable : (prefixWord ++ tailWord_472763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472763).length < 2 ^ (prefixWord ++ tailWord_472763).sum := by decide
  have hdescent : baseEnd_472763 < baseStart_472763 := by decide
  rcases family_descends (prefixWord ++ tailWord_472763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472766 : List Nat := [4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_472766 : Nat := 118140960795 + 472766 * 2 ^ 59
def prefixEnd_472766 : Nat := 4983230072969 + 3 ^ 40 * 472766 * 2
def baseEnd_472766 : Nat := 71927761512178528755791

theorem tailTrace_472766 : CollatzResearch.WordTrace tailWord_472766 prefixEnd_472766 71927761512178528755791 := by
  unfold tailWord_472766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155399075657124856213769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11495461736837999233140101 2155399075657124856213769)
  ·
    refine ⟨1616549306742843642160327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2155399075657124856213769 1616549306742843642160327)
    ·
      refine ⟨2424823960114265463240491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616549306742843642160327 2424823960114265463240491)
      ·
        refine ⟨3637235940171398194860737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424823960114265463240491 3637235940171398194860737)
        ·
          refine ⟨2727926955128548646145553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3637235940171398194860737 2727926955128548646145553)
          ·
            refine ⟨2045945216346411484609165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727926955128548646145553 2045945216346411484609165)
            ·
              refine ⟨767229456129904306728437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2045945216346411484609165 767229456129904306728437)
              ·
                refine ⟨71927761512178528755791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 767229456129904306728437 71927761512178528755791)
                ·
                  rfl

theorem cell20_472766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_472766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472766 prefixEnd_472766 := by exact prefixLift 472766
  have htrace : WordTrace (prefixWord ++ tailWord_472766) baseStart_472766 baseEnd_472766 := by
    simpa [prefixWord, tailWord_472766, baseEnd_472766] using wordTrace_append hprefix tailTrace_472766
  have hstable : (prefixWord ++ tailWord_472766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472766).length < 2 ^ (prefixWord ++ tailWord_472766).sum := by decide
  have hdescent : baseEnd_472766 < baseStart_472766 := by decide
  rcases family_descends (prefixWord ++ tailWord_472766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472811 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_472811 : Nat := 118140960795 + 472811 * 2 ^ 59
def prefixEnd_472811 : Nat := 4983230072969 + 3 ^ 40 * 472811 * 2
def baseEnd_472811 : Nat := 215803823762715429767189

theorem tailTrace_472811 : CollatzResearch.WordTrace tailWord_472811 prefixEnd_472811 215803823762715429767189 := by
  unfold tailWord_472811
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244833890093971535098287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11496555926729314356732191 17244833890093971535098287)
  ·
    refine ⟨25867250835140957302647431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17244833890093971535098287 25867250835140957302647431)
    ·
      refine ⟨38800876252711435953971147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25867250835140957302647431 38800876252711435953971147)
      ·
        refine ⟨58201314379067153930956721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38800876252711435953971147 58201314379067153930956721)
        ·
          refine ⟨43650985784300365448217541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58201314379067153930956721 43650985784300365448217541)
          ·
            refine ⟨8184559834556318521540789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43650985784300365448217541 8184559834556318521540789)
            ·
              refine ⟨767302484489654861394449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8184559834556318521540789 767302484489654861394449)
              ·
                refine ⟨575476863367241146045837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767302484489654861394449 575476863367241146045837)
                ·
                  refine ⟨215803823762715429767189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575476863367241146045837 215803823762715429767189)
                  ·
                    rfl

theorem cell20_472811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_472811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472811 prefixEnd_472811 := by exact prefixLift 472811
  have htrace : WordTrace (prefixWord ++ tailWord_472811) baseStart_472811 baseEnd_472811 := by
    simpa [prefixWord, tailWord_472811, baseEnd_472811] using wordTrace_append hprefix tailTrace_472811
  have hstable : (prefixWord ++ tailWord_472811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472811).length < 2 ^ (prefixWord ++ tailWord_472811).sum := by decide
  have hdescent : baseEnd_472811 < baseStart_472811 := by decide
  rcases family_descends (prefixWord ++ tailWord_472811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472828 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_472828 : Nat := 118140960795 + 472828 * 2 ^ 59
def prefixEnd_472828 : Nat := 4983230072969 + 3 ^ 40 * 472828 * 2
def baseEnd_472828 : Nat := 215811583025938926200453

theorem tailTrace_472828 : CollatzResearch.WordTrace tailWord_472828 prefixEnd_472828 215811583025938926200453 := by
  unfold tailWord_472828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8622726965516191719233569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11496969287354922292311425 8622726965516191719233569)
  ·
    refine ⟨6467045224137143789425177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8622726965516191719233569 6467045224137143789425177)
    ·
      refine ⟨4850283918102857842068883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6467045224137143789425177 4850283918102857842068883)
      ·
        refine ⟨7275425877154286763103325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850283918102857842068883 7275425877154286763103325)
        ·
          refine ⟨2728284703932857536163747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7275425877154286763103325 2728284703932857536163747)
          ·
            refine ⟨4092427055899286304245621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728284703932857536163747 4092427055899286304245621)
            ·
              refine ⟨383665036490558091023027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4092427055899286304245621 383665036490558091023027)
              ·
                refine ⟨575497554735837136534541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383665036490558091023027 575497554735837136534541)
                ·
                  refine ⟨215811583025938926200453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575497554735837136534541 215811583025938926200453)
                  ·
                    rfl

theorem cell20_472828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_472828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472828 prefixEnd_472828 := by exact prefixLift 472828
  have htrace : WordTrace (prefixWord ++ tailWord_472828) baseStart_472828 baseEnd_472828 := by
    simpa [prefixWord, tailWord_472828, baseEnd_472828] using wordTrace_append hprefix tailTrace_472828
  have hstable : (prefixWord ++ tailWord_472828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472828).length < 2 ^ (prefixWord ++ tailWord_472828).sum := by decide
  have hdescent : baseEnd_472828 < baseStart_472828 := by decide
  rcases family_descends (prefixWord ++ tailWord_472828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472842 : List Nat := [3, 1, 2, 2, 1, 3, 4, 4]
def baseStart_472842 : Nat := 118140960795 + 472842 * 2 ^ 59
def prefixEnd_472842 : Nat := 4983230072969 + 3 ^ 40 * 472842 * 2
def baseEnd_472842 : Nat := 71939324335805699911243

theorem tailTrace_472842 : CollatzResearch.WordTrace tailWord_472842 prefixEnd_472842 71939324335805699911243 := by
  unfold tailWord_472842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311491138245415957369195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11497309701987775886317853 4311491138245415957369195)
  ·
    refine ⟨6467236707368123936053793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311491138245415957369195 6467236707368123936053793)
    ·
      refine ⟨4850427530526092952040345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6467236707368123936053793 4850427530526092952040345)
      ·
        refine ⟨3637820647894569714030259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4850427530526092952040345 3637820647894569714030259)
        ·
          refine ⟨5456730971841854571045389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637820647894569714030259 5456730971841854571045389)
          ·
            refine ⟨2046274114440695464142021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5456730971841854571045389 2046274114440695464142021)
            ·
              refine ⟨383676396457630399526629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2046274114440695464142021 383676396457630399526629)
              ·
                refine ⟨71939324335805699911243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383676396457630399526629 71939324335805699911243)
                ·
                  rfl

theorem cell20_472842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_472842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472842 prefixEnd_472842 := by exact prefixLift 472842
  have htrace : WordTrace (prefixWord ++ tailWord_472842) baseStart_472842 baseEnd_472842 := by
    simpa [prefixWord, tailWord_472842, baseEnd_472842] using wordTrace_append hprefix tailTrace_472842
  have hstable : (prefixWord ++ tailWord_472842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472842).length < 2 ^ (prefixWord ++ tailWord_472842).sum := by decide
  have hdescent : baseEnd_472842 < baseStart_472842 := by decide
  rcases family_descends (prefixWord ++ tailWord_472842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472883 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 3]
def baseStart_472883 : Nat := 118140960795 + 472883 * 2 ^ 59
def prefixEnd_472883 : Nat := 4983230072969 + 3 ^ 40 * 472883 * 2
def baseEnd_472883 : Nat := 215836686524603179366895

theorem tailTrace_472883 : CollatzResearch.WordTrace tailWord_472883 prefixEnd_472883 215836686524603179366895 := by
  unfold tailWord_472883
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247459945833127831719303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11498306630555418554479535 17247459945833127831719303)
  ·
    refine ⟨25871189918749691747578955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17247459945833127831719303 25871189918749691747578955)
    ·
      refine ⟨38806784878124537621368433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25871189918749691747578955 38806784878124537621368433)
      ·
        refine ⟨29105088658593403216026325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38806784878124537621368433 29105088658593403216026325)
        ·
          refine ⟨682150515435782887875617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29105088658593403216026325 682150515435782887875617)
          ·
            refine ⟨511612886576837165906713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682150515435782887875617 511612886576837165906713)
            ·
              refine ⟨383709664932627874430035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511612886576837165906713 383709664932627874430035)
              ·
                refine ⟨575564497398941811645053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383709664932627874430035 575564497398941811645053)
                ·
                  refine ⟨215836686524603179366895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575564497398941811645053 215836686524603179366895)
                  ·
                    rfl

theorem cell20_472883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 3].length) (baseStart_472883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472883 prefixEnd_472883 := by exact prefixLift 472883
  have htrace : WordTrace (prefixWord ++ tailWord_472883) baseStart_472883 baseEnd_472883 := by
    simpa [prefixWord, tailWord_472883, baseEnd_472883] using wordTrace_append hprefix tailTrace_472883
  have hstable : (prefixWord ++ tailWord_472883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472883).length < 2 ^ (prefixWord ++ tailWord_472883).sum := by decide
  have hdescent : baseEnd_472883 < baseStart_472883 := by decide
  rcases family_descends (prefixWord ++ tailWord_472883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472924 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 2]
def baseStart_472924 : Nat := 118140960795 + 472924 * 2 ^ 59
def prefixEnd_472924 : Nat := 4983230072969 + 3 ^ 40 * 472924 * 2
def baseEnd_472924 : Nat := 215855400041789259000061

theorem tailTrace_472924 : CollatzResearch.WordTrace tailWord_472924 prefixEnd_472924 215855400041789259000061 := by
  unfold tailWord_472924
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624477669342295916980913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11499303559123061222641217 8624477669342295916980913)
  ·
    refine ⟨6468358252006721937735685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8624477669342295916980913 6468358252006721937735685)
    ·
      refine ⟨1212817172251260363325441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6468358252006721937735685 1212817172251260363325441)
      ·
        refine ⟨909612879188445272494081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1212817172251260363325441 909612879188445272494081)
        ·
          refine ⟨682209659391333954370561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909612879188445272494081 682209659391333954370561)
          ·
            refine ⟨511657244543500465777921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682209659391333954370561 511657244543500465777921)
            ·
              refine ⟨383742933407625349333441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511657244543500465777921 383742933407625349333441)
              ·
                refine ⟨287807200055719012000081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383742933407625349333441 287807200055719012000081)
                ·
                  refine ⟨215855400041789259000061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287807200055719012000081 215855400041789259000061)
                  ·
                    rfl

theorem cell20_472924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_472924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472924 prefixEnd_472924 := by exact prefixLift 472924
  have htrace : WordTrace (prefixWord ++ tailWord_472924) baseStart_472924 baseEnd_472924 := by
    simpa [prefixWord, tailWord_472924, baseEnd_472924] using wordTrace_append hprefix tailTrace_472924
  have hstable : (prefixWord ++ tailWord_472924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472924).length < 2 ^ (prefixWord ++ tailWord_472924).sum := by decide
  have hdescent : baseEnd_472924 < baseStart_472924 := by decide
  rcases family_descends (prefixWord ++ tailWord_472924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472928 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 2]
def baseStart_472928 : Nat := 118140960795 + 472928 * 2 ^ 59
def prefixEnd_472928 : Nat := 4983230072969 + 3 ^ 40 * 472928 * 2
def baseEnd_472928 : Nat := 215857225750783022866711

theorem tailTrace_472928 : CollatzResearch.WordTrace tailWord_472928 prefixEnd_472928 215857225750783022866711 := by
  unfold tailWord_472928
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624550615335050258553719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11499400820446733678071625 8624550615335050258553719)
  ·
    refine ⟨12936825923002575387830579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8624550615335050258553719 12936825923002575387830579)
    ·
      refine ⟨19405238884503863081745869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12936825923002575387830579 19405238884503863081745869)
      ·
        refine ⟨7276964581688948655654701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19405238884503863081745869 7276964581688948655654701)
        ·
          refine ⟨2728861718133355745870513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7276964581688948655654701 2728861718133355745870513)
          ·
            refine ⟨2046646288600016809402885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728861718133355745870513 2046646288600016809402885)
            ·
              refine ⟨383746179112503151763041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2046646288600016809402885 383746179112503151763041)
              ·
                refine ⟨287809634334377363822281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383746179112503151763041 287809634334377363822281)
                ·
                  refine ⟨215857225750783022866711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 287809634334377363822281 215857225750783022866711)
                  ·
                    rfl

theorem cell20_472928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_472928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472928 prefixEnd_472928 := by exact prefixLift 472928
  have htrace : WordTrace (prefixWord ++ tailWord_472928) baseStart_472928 baseEnd_472928 := by
    simpa [prefixWord, tailWord_472928, baseEnd_472928] using wordTrace_append hprefix tailTrace_472928
  have hstable : (prefixWord ++ tailWord_472928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472928).length < 2 ^ (prefixWord ++ tailWord_472928).sum := by decide
  have hdescent : baseEnd_472928 < baseStart_472928 := by decide
  rcases family_descends (prefixWord ++ tailWord_472928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472942 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_472942 : Nat := 118140960795 + 472942 * 2 ^ 59
def prefixEnd_472942 : Nat := 4983230072969 + 3 ^ 40 * 472942 * 2
def baseEnd_472942 : Nat := 215863615732261196399987

theorem tailTrace_472942 : CollatzResearch.WordTrace tailWord_472942 prefixEnd_472942 215863615732261196399987 := by
  unfold tailWord_472942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156201481577422613514635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11499741235079587272078053 2156201481577422613514635)
  ·
    refine ⟨3234302222366133920271953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156201481577422613514635 3234302222366133920271953)
    ·
      refine ⟨2425726666774600440203965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3234302222366133920271953 2425726666774600440203965)
      ·
        refine ⟨909647500040475165076487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2425726666774600440203965 909647500040475165076487)
        ·
          refine ⟨1364471250060712747614731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909647500040475165076487 1364471250060712747614731)
          ·
            refine ⟨2046706875091069121422097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364471250060712747614731 2046706875091069121422097)
            ·
              refine ⟨1535030156318301841066573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046706875091069121422097 1535030156318301841066573)
              ·
                refine ⟨575636308619363190399965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535030156318301841066573 575636308619363190399965)
                ·
                  refine ⟨215863615732261196399987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575636308619363190399965 215863615732261196399987)
                  ·
                    rfl

theorem cell20_472942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_472942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472942 prefixEnd_472942 := by exact prefixLift 472942
  have htrace : WordTrace (prefixWord ++ tailWord_472942) baseStart_472942 baseEnd_472942 := by
    simpa [prefixWord, tailWord_472942, baseEnd_472942] using wordTrace_append hprefix tailTrace_472942
  have hstable : (prefixWord ++ tailWord_472942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472942).length < 2 ^ (prefixWord ++ tailWord_472942).sum := by decide
  have hdescent : baseEnd_472942 < baseStart_472942 := by decide
  rcases family_descends (prefixWord ++ tailWord_472942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472946 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_472946 : Nat := 118140960795 + 472946 * 2 ^ 59
def prefixEnd_472946 : Nat := 4983230072969 + 3 ^ 40 * 472946 * 2
def baseEnd_472946 : Nat := 215865441441254960266637

theorem tailTrace_472946 : CollatzResearch.WordTrace tailWord_472946 prefixEnd_472946 215865441441254960266637 := by
  unfold tailWord_472946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312439436151222397815673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11499838496403259727508461 4312439436151222397815673)
  ·
    refine ⟨3234329577113416798361755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4312439436151222397815673 3234329577113416798361755)
    ·
      refine ⟨4851494365670125197542633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234329577113416798361755 4851494365670125197542633)
      ·
        refine ⟨3638620774252593898156975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4851494365670125197542633 3638620774252593898156975)
        ·
          refine ⟨5457931161378890847235463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638620774252593898156975 5457931161378890847235463)
          ·
            refine ⟨8186896742068336270853195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457931161378890847235463 8186896742068336270853195)
            ·
              refine ⟨12280345113102504406279793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8186896742068336270853195 12280345113102504406279793)
              ·
                refine ⟨9210258834826878304709845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12280345113102504406279793 9210258834826878304709845)
                ·
                  refine ⟨215865441441254960266637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9210258834826878304709845 215865441441254960266637)
                  ·
                    rfl

theorem cell20_472946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_472946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472946 prefixEnd_472946 := by exact prefixLift 472946
  have htrace : WordTrace (prefixWord ++ tailWord_472946) baseStart_472946 baseEnd_472946 := by
    simpa [prefixWord, tailWord_472946, baseEnd_472946] using wordTrace_append hprefix tailTrace_472946
  have hstable : (prefixWord ++ tailWord_472946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472946).length < 2 ^ (prefixWord ++ tailWord_472946).sum := by decide
  have hdescent : baseEnd_472946 < baseStart_472946 := by decide
  rcases family_descends (prefixWord ++ tailWord_472946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_472980 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_472980 : Nat := 118140960795 + 472980 * 2 ^ 59
def prefixEnd_472980 : Nat := 4983230072969 + 3 ^ 40 * 472980 * 2
def baseEnd_472980 : Nat := 215880959967701953133165

theorem tailTrace_472980 : CollatzResearch.WordTrace tailWord_472980 prefixEnd_472980 215880959967701953133165 := by
  unfold tailWord_472980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625498913240856699000197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11500665217654475598666929 8625498913240856699000197)
  ·
    refine ⟨1617281046232660631062537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8625498913240856699000197 1617281046232660631062537)
    ·
      refine ⟨1212960784674495473296903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1617281046232660631062537 1212960784674495473296903)
      ·
        refine ⟨1819441177011743209945355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212960784674495473296903 1819441177011743209945355)
        ·
          refine ⟨2729161765517614814918033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819441177011743209945355 2729161765517614814918033)
          ·
            refine ⟨2046871324138211111188525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729161765517614814918033 2046871324138211111188525)
            ·
              refine ⟨767576746551829166695697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2046871324138211111188525 767576746551829166695697)
              ·
                refine ⟨575682559913871875021773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767576746551829166695697 575682559913871875021773)
                ·
                  refine ⟨215880959967701953133165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575682559913871875021773 215880959967701953133165)
                  ·
                    rfl

theorem cell20_472980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_472980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_472980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_472980 prefixEnd_472980 := by exact prefixLift 472980
  have htrace : WordTrace (prefixWord ++ tailWord_472980) baseStart_472980 baseEnd_472980 := by
    simpa [prefixWord, tailWord_472980, baseEnd_472980] using wordTrace_append hprefix tailTrace_472980
  have hstable : (prefixWord ++ tailWord_472980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_472980).length < 2 ^ (prefixWord ++ tailWord_472980).sum := by decide
  have hdescent : baseEnd_472980 < baseStart_472980 := by decide
  rcases family_descends (prefixWord ++ tailWord_472980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473042 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_473042 : Nat := 118140960795 + 473042 * 2 ^ 59
def prefixEnd_473042 : Nat := 4983230072969 + 3 ^ 40 * 473042 * 2
def baseEnd_473042 : Nat := 215909258457105293066245

theorem tailTrace_473042 : CollatzResearch.WordTrace tailWord_473042 prefixEnd_473042 215909258457105293066245 := by
  unfold tailWord_473042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313314788064274496689345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11502172768171398657838253 4313314788064274496689345)
  ·
    refine ⟨3234986091048205872517009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4313314788064274496689345 3234986091048205872517009)
    ·
      refine ⟨2426239568286154404387757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3234986091048205872517009 2426239568286154404387757)
      ·
        refine ⟨909839838107307901645409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2426239568286154404387757 909839838107307901645409)
        ·
          refine ⟨682379878580480926234057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909839838107307901645409 682379878580480926234057)
          ·
            refine ⟨511784908935360694675543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682379878580480926234057 511784908935360694675543)
            ·
              refine ⟨767677363403041042013315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511784908935360694675543 767677363403041042013315)
              ·
                refine ⟨1151516045104561563019973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767677363403041042013315 1151516045104561563019973)
                ·
                  refine ⟨215909258457105293066245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151516045104561563019973 215909258457105293066245)
                  ·
                    rfl

theorem cell20_473042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_473042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473042 prefixEnd_473042 := by exact prefixLift 473042
  have htrace : WordTrace (prefixWord ++ tailWord_473042) baseStart_473042 baseEnd_473042 := by
    simpa [prefixWord, tailWord_473042, baseEnd_473042] using wordTrace_append hprefix tailTrace_473042
  have hstable : (prefixWord ++ tailWord_473042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473042).length < 2 ^ (prefixWord ++ tailWord_473042).sum := by decide
  have hdescent : baseEnd_473042 < baseStart_473042 := by decide
  rcases family_descends (prefixWord ++ tailWord_473042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473052 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 3]
def baseStart_473052 : Nat := 118140960795 + 473052 * 2 ^ 59
def prefixEnd_473052 : Nat := 4983230072969 + 3 ^ 40 * 473052 * 2
def baseEnd_473052 : Nat := 215913822729589702732871

theorem tailTrace_473052 : CollatzResearch.WordTrace tailWord_473052 prefixEnd_473052 215913822729589702732871 := by
  unfold tailWord_473052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626811941110434847310705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11502415921480579796414273 8626811941110434847310705)
  ·
    refine ⟨6470108955832826135483029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8626811941110434847310705 6470108955832826135483029)
    ·
      refine ⟨303286357304663725100767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6470108955832826135483029 303286357304663725100767)
      ·
        refine ⟨454929535956995587651151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303286357304663725100767 454929535956995587651151)
        ·
          refine ⟨682394303935493381476727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454929535956995587651151 682394303935493381476727)
          ·
            refine ⟨1023591455903240072215091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682394303935493381476727 1023591455903240072215091)
            ·
              refine ⟨1535387183854860108322637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023591455903240072215091 1535387183854860108322637)
              ·
                refine ⟨575770193945572540620989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535387183854860108322637 575770193945572540620989)
                ·
                  refine ⟨215913822729589702732871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575770193945572540620989 215913822729589702732871)
                  ·
                    rfl

theorem cell20_473052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_473052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473052 prefixEnd_473052 := by exact prefixLift 473052
  have htrace : WordTrace (prefixWord ++ tailWord_473052) baseStart_473052 baseEnd_473052 := by
    simpa [prefixWord, tailWord_473052, baseEnd_473052] using wordTrace_append hprefix tailTrace_473052
  have hstable : (prefixWord ++ tailWord_473052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473052).length < 2 ^ (prefixWord ++ tailWord_473052).sum := by decide
  have hdescent : baseEnd_473052 < baseStart_473052 := by decide
  rcases family_descends (prefixWord ++ tailWord_473052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473067 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_473067 : Nat := 118140960795 + 473067 * 2 ^ 59
def prefixEnd_473067 : Nat := 4983230072969 + 3 ^ 40 * 473067 * 2
def baseEnd_473067 : Nat := 215920669138316317232809

theorem tailTrace_473067 : CollatzResearch.WordTrace tailWord_473067 prefixEnd_473067 215920669138316317232809 := by
  unfold tailWord_473067
  simp only [CollatzResearch.WordTrace]
  refine ⟨17254170977166527256417455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11502780651444351504278303 17254170977166527256417455)
  ·
    refine ⟨25881256465749790884626183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17254170977166527256417455 25881256465749790884626183)
    ·
      refine ⟨38821884698624686326939275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25881256465749790884626183 38821884698624686326939275)
      ·
        refine ⟨58232827047937029490408913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38821884698624686326939275 58232827047937029490408913)
        ·
          refine ⟨43674620285952772117806685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58232827047937029490408913 43674620285952772117806685)
          ·
            refine ⟨16377982607232289544177507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43674620285952772117806685 16377982607232289544177507)
            ·
              refine ⟨24566973910848434316266261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16377982607232289544177507 24566973910848434316266261)
              ·
                refine ⟨1151576902071020358574981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24566973910848434316266261 1151576902071020358574981)
                ·
                  refine ⟨215920669138316317232809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151576902071020358574981 215920669138316317232809)
                  ·
                    rfl

theorem cell20_473067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_473067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473067 prefixEnd_473067 := by exact prefixLift 473067
  have htrace : WordTrace (prefixWord ++ tailWord_473067) baseStart_473067 baseEnd_473067 := by
    simpa [prefixWord, tailWord_473067, baseEnd_473067] using wordTrace_append hprefix tailTrace_473067
  have hstable : (prefixWord ++ tailWord_473067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473067).length < 2 ^ (prefixWord ++ tailWord_473067).sum := by decide
  have hdescent : baseEnd_473067 < baseStart_473067 := by decide
  rcases family_descends (prefixWord ++ tailWord_473067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473122 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_473122 : Nat := 118140960795 + 473122 * 2 ^ 59
def prefixEnd_473122 : Nat := 4983230072969 + 3 ^ 40 * 473122 * 2
def baseEnd_473122 : Nat := 215945772636980570399251

theorem tailTrace_473122 : CollatzResearch.WordTrace tailWord_473122 prefixEnd_473122 215945772636980570399251 := by
  unfold tailWord_473122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314044247991817912417405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11504117994644847766446413 4314044247991817912417405)
  ·
    refine ⟨1617766592996931717156527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4314044247991817912417405 1617766592996931717156527)
    ·
      refine ⟨2426649889495397575734791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1617766592996931717156527 2426649889495397575734791)
      ·
        refine ⟨3639974834243096363602187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426649889495397575734791 3639974834243096363602187)
        ·
          refine ⟨5459962251364644545403281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639974834243096363602187 5459962251364644545403281)
          ·
            refine ⟨4094971688523483409052461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459962251364644545403281 4094971688523483409052461)
            ·
              refine ⟨1535614383196306278394673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094971688523483409052461 1535614383196306278394673)
              ·
                refine ⟨1151710787397229708796005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535614383196306278394673 1151710787397229708796005)
                ·
                  refine ⟨215945772636980570399251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1151710787397229708796005 215945772636980570399251)
                  ·
                    rfl

theorem cell20_473122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_473122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473122 prefixEnd_473122 := by exact prefixLift 473122
  have htrace : WordTrace (prefixWord ++ tailWord_473122) baseStart_473122 baseEnd_473122 := by
    simpa [prefixWord, tailWord_473122, baseEnd_473122] using wordTrace_append hprefix tailTrace_473122
  have hstable : (prefixWord ++ tailWord_473122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473122).length < 2 ^ (prefixWord ++ tailWord_473122).sum := by decide
  have hdescent : baseEnd_473122 < baseStart_473122 := by decide
  rcases family_descends (prefixWord ++ tailWord_473122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473153 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_473153 : Nat := 118140960795 + 473153 * 2 ^ 59
def prefixEnd_473153 : Nat := 4983230072969 + 3 ^ 40 * 473153 * 2
def baseEnd_473153 : Nat := 215959921881682240365791

theorem tailTrace_473153 : CollatzResearch.WordTrace tailWord_473153 prefixEnd_473153 215959921881682240365791 := by
  unfold tailWord_473153
  simp only [CollatzResearch.WordTrace]
  refine ⟨17257307654854963944048113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11504871769903309296032075 17257307654854963944048113)
  ·
    refine ⟨12942980741141222958036085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17257307654854963944048113 12942980741141222958036085)
    ·
      refine ⟨1213404444481989652315883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12942980741141222958036085 1213404444481989652315883)
      ·
        refine ⟨1820106666722984478473825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213404444481989652315883 1820106666722984478473825)
        ·
          refine ⟨1365080000042238358855369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820106666722984478473825 1365080000042238358855369)
          ·
            refine ⟨1023810000031678769141527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365080000042238358855369 1023810000031678769141527)
            ·
              refine ⟨1535715000047518153712291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023810000031678769141527 1535715000047518153712291)
              ·
                refine ⟨2303572500071277230568437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535715000047518153712291 2303572500071277230568437)
                ·
                  refine ⟨215959921881682240365791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2303572500071277230568437 215959921881682240365791)
                  ·
                    rfl

theorem cell20_473153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_473153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473153 prefixEnd_473153 := by exact prefixLift 473153
  have htrace : WordTrace (prefixWord ++ tailWord_473153) baseStart_473153 baseEnd_473153 := by
    simpa [prefixWord, tailWord_473153, baseEnd_473153] using wordTrace_append hprefix tailTrace_473153
  have hstable : (prefixWord ++ tailWord_473153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473153).length < 2 ^ (prefixWord ++ tailWord_473153).sum := by decide
  have hdescent : baseEnd_473153 < baseStart_473153 := by decide
  rcases family_descends (prefixWord ++ tailWord_473153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473184 : List Nat := [2, 1, 1, 3, 2, 5, 2, 4]
def baseStart_473184 : Nat := 118140960795 + 473184 * 2 ^ 59
def prefixEnd_473184 : Nat := 4983230072969 + 3 ^ 40 * 473184 * 2
def baseEnd_473184 : Nat := 71991357042127970110777

theorem tailTrace_473184 : CollatzResearch.WordTrace tailWord_473184 prefixEnd_473184 71991357042127970110777 := by
  unfold tailWord_473184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629219158871328119213303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11505625545161770825617737 8629219158871328119213303)
  ·
    refine ⟨12943828738306992178819955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8629219158871328119213303 12943828738306992178819955)
    ·
      refine ⟨19415743107460488268229933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12943828738306992178819955 19415743107460488268229933)
      ·
        refine ⟨7280903665297683100586225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19415743107460488268229933 7280903665297683100586225)
        ·
          refine ⟨5460677748973262325439669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7280903665297683100586225 5460677748973262325439669)
          ·
            refine ⟨511938538966243343009969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5460677748973262325439669 511938538966243343009969)
            ·
              refine ⟨383953904224682507257477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511938538966243343009969 383953904224682507257477)
              ·
                refine ⟨71991357042127970110777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383953904224682507257477 71991357042127970110777)
                ·
                  rfl

theorem cell20_473184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_473184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473184 prefixEnd_473184 := by exact prefixLift 473184
  have htrace : WordTrace (prefixWord ++ tailWord_473184) baseStart_473184 baseEnd_473184 := by
    simpa [prefixWord, tailWord_473184, baseEnd_473184] using wordTrace_append hprefix tailTrace_473184
  have hstable : (prefixWord ++ tailWord_473184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473184).length < 2 ^ (prefixWord ++ tailWord_473184).sum := by decide
  have hdescent : baseEnd_473184 < baseStart_473184 := by decide
  rcases family_descends (prefixWord ++ tailWord_473184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473212 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_473212 : Nat := 118140960795 + 473212 * 2 ^ 59
def prefixEnd_473212 : Nat := 4983230072969 + 3 ^ 40 * 473212 * 2
def baseEnd_473212 : Nat := 215986851089340257398883

theorem tailTrace_473212 : CollatzResearch.WordTrace tailWord_473212 prefixEnd_473212 215986851089340257398883 := by
  unfold tailWord_473212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8629729780820608510222945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11506306374427478013630593 8629729780820608510222945)
  ·
    refine ⟨6472297335615456382667209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8629729780820608510222945 6472297335615456382667209)
    ·
      refine ⟨4854223001711592287000407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6472297335615456382667209 4854223001711592287000407)
      ·
        refine ⟨7281334502567388430500611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854223001711592287000407 7281334502567388430500611)
        ·
          refine ⟨10922001753851082645750917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281334502567388430500611 10922001753851082645750917)
          ·
            refine ⟨2047875328847077996078297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10922001753851082645750917 2047875328847077996078297)
            ·
              refine ⟨1535906496635308497058723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047875328847077996078297 1535906496635308497058723)
              ·
                refine ⟨2303859744952962745588085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535906496635308497058723 2303859744952962745588085)
                ·
                  refine ⟨215986851089340257398883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2303859744952962745588085 215986851089340257398883)
                  ·
                    rfl

theorem cell20_473212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_473212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473212 prefixEnd_473212 := by exact prefixLift 473212
  have htrace : WordTrace (prefixWord ++ tailWord_473212) baseStart_473212 baseEnd_473212 := by
    simpa [prefixWord, tailWord_473212, baseEnd_473212] using wordTrace_append hprefix tailTrace_473212
  have hstable : (prefixWord ++ tailWord_473212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473212).length < 2 ^ (prefixWord ++ tailWord_473212).sum := by decide
  have hdescent : baseEnd_473212 < baseStart_473212 := by decide
  rcases family_descends (prefixWord ++ tailWord_473212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473295 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_473295 : Nat := 118140960795 + 473295 * 2 ^ 59
def prefixEnd_473295 : Nat := 4983230072969 + 3 ^ 40 * 473295 * 2
def baseEnd_473295 : Nat := 216024734550960857631877

theorem tailTrace_473295 : CollatzResearch.WordTrace tailWord_473295 prefixEnd_473295 216024734550960857631877 := by
  unfold tailWord_473295
  simp only [CollatzResearch.WordTrace]
  refine ⟨17262486820340522195717339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11508324546893681463811559 17262486820340522195717339)
  ·
    refine ⟨25893730230510783293576009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17262486820340522195717339 25893730230510783293576009)
    ·
      refine ⟨19420297672883087470182007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25893730230510783293576009 19420297672883087470182007)
      ·
        refine ⟨29130446509324631205273011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19420297672883087470182007 29130446509324631205273011)
        ·
          refine ⟨43695669763986946807909517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29130446509324631205273011 43695669763986946807909517)
          ·
            refine ⟨16385876161495105052966069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43695669763986946807909517 16385876161495105052966069)
            ·
              refine ⟨1536175890140166098715569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16385876161495105052966069 1536175890140166098715569)
              ·
                refine ⟨1152131917605124574036677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536175890140166098715569 1152131917605124574036677)
                ·
                  refine ⟨216024734550960857631877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1152131917605124574036677 216024734550960857631877)
                  ·
                    rfl

theorem cell20_473295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_473295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473295 prefixEnd_473295 := by exact prefixLift 473295
  have htrace : WordTrace (prefixWord ++ tailWord_473295) baseStart_473295 baseEnd_473295 := by
    simpa [prefixWord, tailWord_473295, baseEnd_473295] using wordTrace_append hprefix tailTrace_473295
  have hstable : (prefixWord ++ tailWord_473295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473295).length < 2 ^ (prefixWord ++ tailWord_473295).sum := by decide
  have hdescent : baseEnd_473295 < baseStart_473295 := by decide
  rcases family_descends (prefixWord ++ tailWord_473295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473298 : List Nat := [3, 2, 2, 2, 1, 3, 3, 4]
def baseStart_473298 : Nat := 118140960795 + 473298 * 2 ^ 59
def prefixEnd_473298 : Nat := 4983230072969 + 3 ^ 40 * 473298 * 2
def baseEnd_473298 : Nat := 72008701277568726843955

theorem tailTrace_473298 : CollatzResearch.WordTrace tailWord_473298 prefixEnd_473298 72008701277568726843955 := by
  unfold tailWord_473298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315649059832413427019137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11508397492886435805384365 4315649059832413427019137)
  ·
    refine ⟨3236736794874310070264353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4315649059832413427019137 3236736794874310070264353)
    ·
      refine ⟨2427552596155732552698265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236736794874310070264353 2427552596155732552698265)
      ·
        refine ⟨1820664447116799414523699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2427552596155732552698265 1820664447116799414523699)
        ·
          refine ⟨2730996670675199121785549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820664447116799414523699 2730996670675199121785549)
          ·
            refine ⟨1024123751503199670669581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2730996670675199121785549 1024123751503199670669581)
            ·
              refine ⟨384046406813699876501093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1024123751503199670669581 384046406813699876501093)
              ·
                refine ⟨72008701277568726843955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384046406813699876501093 72008701277568726843955)
                ·
                  rfl

theorem cell20_473298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_473298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473298 prefixEnd_473298 := by exact prefixLift 473298
  have htrace : WordTrace (prefixWord ++ tailWord_473298) baseStart_473298 baseEnd_473298 := by
    simpa [prefixWord, tailWord_473298, baseEnd_473298] using wordTrace_append hprefix tailTrace_473298
  have hstable : (prefixWord ++ tailWord_473298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473298).length < 2 ^ (prefixWord ++ tailWord_473298).sum := by decide
  have hdescent : baseEnd_473298 < baseStart_473298 := by decide
  rcases family_descends (prefixWord ++ tailWord_473298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473319 : List Nat := [1, 1, 5, 3, 1, 2, 7]
def baseStart_473319 : Nat := 118140960795 + 473319 * 2 ^ 59
def prefixEnd_473319 : Nat := 4983230072969 + 3 ^ 40 * 473319 * 2
def baseEnd_473319 : Nat := 24003965422769271203531

theorem tailTrace_473319 : CollatzResearch.WordTrace tailWord_473319 prefixEnd_473319 24003965422769271203531 := by
  unfold tailWord_473319
  simp only [CollatzResearch.WordTrace]
  refine ⟨17263362172253574294591011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11508908114835716196394007 17263362172253574294591011)
  ·
    refine ⟨25895043258380361441886517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17263362172253574294591011 25895043258380361441886517)
    ·
      refine ⟨2427660305473158885176861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25895043258380361441886517 2427660305473158885176861)
      ·
        refine ⟨910372614552434581941323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2427660305473158885176861 910372614552434581941323)
        ·
          refine ⟨1365558921828651872911985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910372614552434581941323 1365558921828651872911985)
          ·
            refine ⟨1024169191371488904683989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365558921828651872911985 1024169191371488904683989)
            ·
              refine ⟨24003965422769271203531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1024169191371488904683989 24003965422769271203531)
              ·
                rfl

theorem cell20_473319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_473319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473319 prefixEnd_473319 := by exact prefixLift 473319
  have htrace : WordTrace (prefixWord ++ tailWord_473319) baseStart_473319 baseEnd_473319 := by
    simpa [prefixWord, tailWord_473319, baseEnd_473319] using wordTrace_append hprefix tailTrace_473319
  have hstable : (prefixWord ++ tailWord_473319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473319).length < 2 ^ (prefixWord ++ tailWord_473319).sum := by decide
  have hdescent : baseEnd_473319 < baseStart_473319 := by decide
  rcases family_descends (prefixWord ++ tailWord_473319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473343 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 3]
def baseStart_473343 : Nat := 118140960795 + 473343 * 2 ^ 59
def prefixEnd_473343 : Nat := 4983230072969 + 3 ^ 40 * 473343 * 2
def baseEnd_473343 : Nat := 216046643058886024031681

theorem tailTrace_473343 : CollatzResearch.WordTrace tailWord_473343 prefixEnd_473343 216046643058886024031681 := by
  unfold tailWord_473343
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264237524166626393464683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11509491682777750928976455 17264237524166626393464683)
  ·
    refine ⟨25896356286249939590197025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264237524166626393464683 25896356286249939590197025)
    ·
      refine ⟨19422267214687454692647769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25896356286249939590197025 19422267214687454692647769)
      ·
        refine ⟨14566700411015591019485827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19422267214687454692647769 14566700411015591019485827)
        ·
          refine ⟨21850050616523386529228741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14566700411015591019485827 21850050616523386529228741)
          ·
            refine ⟨4096884490598134974230389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21850050616523386529228741 4096884490598134974230389)
            ·
              refine ⟨384082920993575153834099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4096884490598134974230389 384082920993575153834099)
              ·
                refine ⟨576124381490362730751149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384082920993575153834099 576124381490362730751149)
                ·
                  refine ⟨216046643058886024031681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576124381490362730751149 216046643058886024031681)
                  ·
                    rfl

theorem cell20_473343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_473343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473343 prefixEnd_473343 := by exact prefixLift 473343
  have htrace : WordTrace (prefixWord ++ tailWord_473343) baseStart_473343 baseEnd_473343 := by
    simpa [prefixWord, tailWord_473343, baseEnd_473343] using wordTrace_append hprefix tailTrace_473343
  have hstable : (prefixWord ++ tailWord_473343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473343).length < 2 ^ (prefixWord ++ tailWord_473343).sum := by decide
  have hdescent : baseEnd_473343 < baseStart_473343 := by decide
  rcases family_descends (prefixWord ++ tailWord_473343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473367 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 2]
def baseStart_473367 : Nat := 118140960795 + 473367 * 2 ^ 59
def prefixEnd_473367 : Nat := 4983230072969 + 3 ^ 40 * 473367 * 2
def baseEnd_473367 : Nat := 216057597312848607231583

theorem tailTrace_473367 : CollatzResearch.WordTrace tailWord_473367 prefixEnd_473367 216057597312848607231583 := by
  unfold tailWord_473367
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265112876079678492338355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11510075250719785661558903 17265112876079678492338355)
  ·
    refine ⟨25897669314119517738507533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17265112876079678492338355 25897669314119517738507533)
    ·
      refine ⟨9711625992794819151940325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25897669314119517738507533 9711625992794819151940325)
      ·
        refine ⟨1820929873649028590988811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9711625992794819151940325 1820929873649028590988811)
        ·
          refine ⟨2731394810473542886483217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820929873649028590988811 2731394810473542886483217)
          ·
            refine ⟨2048546107855157164862413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731394810473542886483217 2048546107855157164862413)
            ·
              refine ⟨768204790445683936823405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2048546107855157164862413 768204790445683936823405)
              ·
                refine ⟨288076796417131476308777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 768204790445683936823405 288076796417131476308777)
                ·
                  refine ⟨216057597312848607231583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288076796417131476308777 216057597312848607231583)
                  ·
                    rfl

theorem cell20_473367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 2].length) (baseStart_473367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473367 prefixEnd_473367 := by exact prefixLift 473367
  have htrace : WordTrace (prefixWord ++ tailWord_473367) baseStart_473367 baseEnd_473367 := by
    simpa [prefixWord, tailWord_473367, baseEnd_473367] using wordTrace_append hprefix tailTrace_473367
  have hstable : (prefixWord ++ tailWord_473367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473367).length < 2 ^ (prefixWord ++ tailWord_473367).sum := by decide
  have hdescent : baseEnd_473367 < baseStart_473367 := by decide
  rcases family_descends (prefixWord ++ tailWord_473367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473374 : List Nat := [4, 3, 2, 1, 1, 1, 8]
def baseStart_473374 : Nat := 118140960795 + 473374 * 2 ^ 59
def prefixEnd_473374 : Nat := 4983230072969 + 3 ^ 40 * 473374 * 2
def baseEnd_473374 : Nat := 24006754700398632666469

theorem tailTrace_473374 : CollatzResearch.WordTrace tailWord_473374 prefixEnd_473374 24006754700398632666469 := by
  unfold tailWord_473374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158171023381789835980397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11510245458036212458562117 2158171023381789835980397)
  ·
    refine ⟨809314133768171188492649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2158171023381789835980397 809314133768171188492649)
    ·
      refine ⟨606985600326128391369487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 809314133768171188492649 606985600326128391369487)
      ·
        refine ⟨910478400489192587054231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606985600326128391369487 910478400489192587054231)
        ·
          refine ⟨1365717600733788880581347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910478400489192587054231 1365717600733788880581347)
          ·
            refine ⟨2048576401100683320872021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365717600733788880581347 2048576401100683320872021)
            ·
              refine ⟨24006754700398632666469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2048576401100683320872021 24006754700398632666469)
              ·
                rfl

theorem cell20_473374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 8].length) (baseStart_473374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473374 prefixEnd_473374 := by exact prefixLift 473374
  have htrace : WordTrace (prefixWord ++ tailWord_473374) baseStart_473374 baseEnd_473374 := by
    simpa [prefixWord, tailWord_473374, baseEnd_473374] using wordTrace_append hprefix tailTrace_473374
  have hstable : (prefixWord ++ tailWord_473374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473374).length < 2 ^ (prefixWord ++ tailWord_473374).sum := by decide
  have hdescent : baseEnd_473374 < baseStart_473374 := by decide
  rcases family_descends (prefixWord ++ tailWord_473374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473384 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 4]
def baseStart_473384 : Nat := 118140960795 + 473384 * 2 ^ 59
def prefixEnd_473384 : Nat := 4983230072969 + 3 ^ 40 * 473384 * 2
def baseEnd_473384 : Nat := 216065356576072103664847

theorem tailTrace_473384 : CollatzResearch.WordTrace tailWord_473384 prefixEnd_473384 216065356576072103664847 := by
  unfold tailWord_473384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632866458509045197853603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11510488611345393597138137 8632866458509045197853603)
  ·
    refine ⟨12949299687763567796780405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8632866458509045197853603 12949299687763567796780405)
    ·
      refine ⟨1213996845727834480948163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12949299687763567796780405 1213996845727834480948163)
      ·
        refine ⟨1820995268591751721422245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213996845727834480948163 1820995268591751721422245)
        ·
          refine ⟨341436612860953447766671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1820995268591751721422245 341436612860953447766671)
          ·
            refine ⟨512154919291430171650007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341436612860953447766671 512154919291430171650007)
            ·
              refine ⟨768232378937145257475011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512154919291430171650007 768232378937145257475011)
              ·
                refine ⟨1152348568405717886212517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768232378937145257475011 1152348568405717886212517)
                ·
                  refine ⟨216065356576072103664847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1152348568405717886212517 216065356576072103664847)
                  ·
                    rfl

theorem cell20_473384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_473384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473384 prefixEnd_473384 := by exact prefixLift 473384
  have htrace : WordTrace (prefixWord ++ tailWord_473384) baseStart_473384 baseEnd_473384 := by
    simpa [prefixWord, tailWord_473384, baseEnd_473384] using wordTrace_append hprefix tailTrace_473384
  have hstable : (prefixWord ++ tailWord_473384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473384).length < 2 ^ (prefixWord ++ tailWord_473384).sum := by decide
  have hdescent : baseEnd_473384 < baseStart_473384 := by decide
  rcases family_descends (prefixWord ++ tailWord_473384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473388 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 2]
def baseStart_473388 : Nat := 118140960795 + 473388 * 2 ^ 59
def prefixEnd_473388 : Nat := 4983230072969 + 3 ^ 40 * 473388 * 2
def baseEnd_473388 : Nat := 216067182285065867531497

theorem tailTrace_473388 : CollatzResearch.WordTrace tailWord_473388 prefixEnd_473388 216067182285065867531497 := by
  unfold tailWord_473388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632939404501799539426409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11510585872669066052568545 8632939404501799539426409)
  ·
    refine ⟨6474704553376349654569807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8632939404501799539426409 6474704553376349654569807)
    ·
      refine ⟨9712056830064524481854711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6474704553376349654569807 9712056830064524481854711)
      ·
        refine ⟨14568085245096786722782067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9712056830064524481854711 14568085245096786722782067)
        ·
          refine ⟨21852127867645180084173101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568085245096786722782067 21852127867645180084173101)
          ·
            refine ⟨8194547950366942531564913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21852127867645180084173101 8194547950366942531564913)
            ·
              refine ⟨6145910962775206898673685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194547950366942531564913 6145910962775206898673685)
              ·
                refine ⟨288089576380087823375329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6145910962775206898673685 288089576380087823375329)
                ·
                  refine ⟨216067182285065867531497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288089576380087823375329 216067182285065867531497)
                  ·
                    rfl

theorem cell20_473388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_473388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473388 prefixEnd_473388 := by exact prefixLift 473388
  have htrace : WordTrace (prefixWord ++ tailWord_473388) baseStart_473388 baseEnd_473388 := by
    simpa [prefixWord, tailWord_473388, baseEnd_473388] using wordTrace_append hprefix tailTrace_473388
  have hstable : (prefixWord ++ tailWord_473388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473388).length < 2 ^ (prefixWord ++ tailWord_473388).sum := by decide
  have hdescent : baseEnd_473388 < baseStart_473388 := by decide
  rcases family_descends (prefixWord ++ tailWord_473388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473416 : List Nat := [2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_473416 : Nat := 118140960795 + 473416 * 2 ^ 59
def prefixEnd_473416 : Nat := 4983230072969 + 3 ^ 40 * 473416 * 2
def baseEnd_473416 : Nat := 72026654082674071532683

theorem tailTrace_473416 : CollatzResearch.WordTrace tailWord_473416 prefixEnd_473416 72026654082674071532683 := by
  unfold tailWord_473416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633450026451079930436051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11511266701934773240581401 8633450026451079930436051)
  ·
    refine ⟨12950175039676619895654077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8633450026451079930436051 12950175039676619895654077)
    ·
      refine ⟨4856315639878732460870279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12950175039676619895654077 4856315639878732460870279)
      ·
        refine ⟨7284473459818098691305419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856315639878732460870279 7284473459818098691305419)
        ·
          refine ⟨10926710189727148036958129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7284473459818098691305419 10926710189727148036958129)
          ·
            refine ⟨8195032642295361027718597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10926710189727148036958129 8195032642295361027718597)
            ·
              refine ⟨1536568620430380192697237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8195032642295361027718597 1536568620430380192697237)
              ·
                refine ⟨72026654082674071532683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1536568620430380192697237 72026654082674071532683)
                ·
                  rfl

theorem cell20_473416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_473416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473416 prefixEnd_473416 := by exact prefixLift 473416
  have htrace : WordTrace (prefixWord ++ tailWord_473416) baseStart_473416 baseEnd_473416 := by
    simpa [prefixWord, tailWord_473416, baseEnd_473416] using wordTrace_append hprefix tailTrace_473416
  have hstable : (prefixWord ++ tailWord_473416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473416).length < 2 ^ (prefixWord ++ tailWord_473416).sum := by decide
  have hdescent : baseEnd_473416 < baseStart_473416 := by decide
  rcases family_descends (prefixWord ++ tailWord_473416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473423 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_473423 : Nat := 118140960795 + 473423 * 2 ^ 59
def prefixEnd_473423 : Nat := 4983230072969 + 3 ^ 40 * 473423 * 2
def baseEnd_473423 : Nat := 216083157238761301364687

theorem tailTrace_473423 : CollatzResearch.WordTrace tailWord_473423 prefixEnd_473423 216083157238761301364687 := by
  unfold tailWord_473423
  simp only [CollatzResearch.WordTrace]
  refine ⟨17267155363876800056376923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11511436909251200037584615 17267155363876800056376923)
  ·
    refine ⟨25900733045815200084565385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17267155363876800056376923 25900733045815200084565385)
    ·
      refine ⟨19425549784361400063424039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25900733045815200084565385 19425549784361400063424039)
      ·
        refine ⟨29138324676542100095136059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19425549784361400063424039 29138324676542100095136059)
        ·
          refine ⟨43707487014813150142704089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29138324676542100095136059 43707487014813150142704089)
          ·
            refine ⟨32780615261109862607028067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43707487014813150142704089 32780615261109862607028067)
            ·
              refine ⟨49170922891664793910542101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32780615261109862607028067 49170922891664793910542101)
              ·
                refine ⟨2304887010546787214556661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49170922891664793910542101 2304887010546787214556661)
                ·
                  refine ⟨216083157238761301364687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2304887010546787214556661 216083157238761301364687)
                  ·
                    rfl

theorem cell20_473423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_473423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473423 prefixEnd_473423 := by exact prefixLift 473423
  have htrace : WordTrace (prefixWord ++ tailWord_473423) baseStart_473423 baseEnd_473423 := by
    simpa [prefixWord, tailWord_473423, baseEnd_473423] using wordTrace_append hprefix tailTrace_473423
  have hstable : (prefixWord ++ tailWord_473423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473423).length < 2 ^ (prefixWord ++ tailWord_473423).sum := by decide
  have hdescent : baseEnd_473423 < baseStart_473423 := by decide
  rcases family_descends (prefixWord ++ tailWord_473423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473450 : List Nat := [3, 1, 3, 3, 1, 3, 1, 5]
def baseStart_473450 : Nat := 118140960795 + 473450 * 2 ^ 59
def prefixEnd_473450 : Nat := 4983230072969 + 3 ^ 40 * 473450 * 2
def baseEnd_473450 : Nat := 72031826924823069154859

theorem tailTrace_473450 : CollatzResearch.WordTrace tailWord_473450 prefixEnd_473450 72031826924823069154859 := by
  unfold tailWord_473450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317035033694745916902451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11512093423185989111739869 4317035033694745916902451)
  ·
    refine ⟨6475552550542118875353677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317035033694745916902451 6475552550542118875353677)
    ·
      refine ⟨2428332206453294578257629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6475552550542118875353677 2428332206453294578257629)
      ·
        refine ⟨910624577419985466846611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2428332206453294578257629 910624577419985466846611)
        ·
          refine ⟨1365936866129978200269917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910624577419985466846611 1365936866129978200269917)
          ·
            refine ⟨512226324798741825101219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1365936866129978200269917 512226324798741825101219)
            ·
              refine ⟨768339487198112737651829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512226324798741825101219 768339487198112737651829)
              ·
                refine ⟨72031826924823069154859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 768339487198112737651829 72031826924823069154859)
                ·
                  rfl

theorem cell20_473450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_473450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473450 prefixEnd_473450 := by exact prefixLift 473450
  have htrace : WordTrace (prefixWord ++ tailWord_473450) baseStart_473450 baseEnd_473450 := by
    simpa [prefixWord, tailWord_473450, baseEnd_473450] using wordTrace_append hprefix tailTrace_473450
  have hstable : (prefixWord ++ tailWord_473450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473450).length < 2 ^ (prefixWord ++ tailWord_473450).sum := by decide
  have hdescent : baseEnd_473450 < baseStart_473450 := by decide
  rcases family_descends (prefixWord ++ tailWord_473450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473481 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 2]
def baseStart_473481 : Nat := 118140960795 + 473481 * 2 ^ 59
def prefixEnd_473481 : Nat := 4983230072969 + 3 ^ 40 * 473481 * 2
def baseEnd_473481 : Nat := 216109630019170877431117

theorem tailTrace_473481 : CollatzResearch.WordTrace tailWord_473481 prefixEnd_473481 216109630019170877431117 := by
  unfold tailWord_473481
  simp only [CollatzResearch.WordTrace]
  refine ⟨17269270797666675961988297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11512847198444450641325531 17269270797666675961988297)
  ·
    refine ⟨12951953098250006971491223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17269270797666675961988297 12951953098250006971491223)
    ·
      refine ⟨19427929647375010457236835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12951953098250006971491223 19427929647375010457236835)
      ·
        refine ⟨29141894471062515685855253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19427929647375010457236835 29141894471062515685855253)
        ·
          refine ⟨1366026303331055422774465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29141894471062515685855253 1366026303331055422774465)
          ·
            refine ⟨1024519727498291567080849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1366026303331055422774465 1024519727498291567080849)
            ·
              refine ⟨768389795623718675310637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024519727498291567080849 768389795623718675310637)
              ·
                refine ⟨288146173358894503241489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 768389795623718675310637 288146173358894503241489)
                ·
                  refine ⟨216109630019170877431117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288146173358894503241489 216109630019170877431117)
                  ·
                    rfl

theorem cell20_473481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_473481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473481 prefixEnd_473481 := by exact prefixLift 473481
  have htrace : WordTrace (prefixWord ++ tailWord_473481) baseStart_473481 baseEnd_473481 := by
    simpa [prefixWord, tailWord_473481, baseEnd_473481] using wordTrace_append hprefix tailTrace_473481
  have hstable : (prefixWord ++ tailWord_473481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473481).length < 2 ^ (prefixWord ++ tailWord_473481).sum := by decide
  have hdescent : baseEnd_473481 < baseStart_473481 := by decide
  rcases family_descends (prefixWord ++ tailWord_473481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473568 : List Nat := [2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_473568 : Nat := 118140960795 + 473568 * 2 ^ 59
def prefixEnd_473568 : Nat := 4983230072969 + 3 ^ 40 * 473568 * 2
def baseEnd_473568 : Nat := 72049779729928413843587

theorem tailTrace_473568 : CollatzResearch.WordTrace tailWord_473568 prefixEnd_473568 72049779729928413843587 := by
  unfold tailWord_473568
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636221974175744910202679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11514962632234326546936905 8636221974175744910202679)
  ·
    refine ⟨12954332961263617365304019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8636221974175744910202679 12954332961263617365304019)
    ·
      refine ⟨19431499441895426047956029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12954332961263617365304019 19431499441895426047956029)
      ·
        refine ⟨7286812290710784767983511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19431499441895426047956029 7286812290710784767983511)
        ·
          refine ⟨10930218436066177151975267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286812290710784767983511 10930218436066177151975267)
          ·
            refine ⟨16395327654099265727962901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10930218436066177151975267 16395327654099265727962901)
            ·
              refine ⟨768530983785903080998261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16395327654099265727962901 768530983785903080998261)
              ·
                refine ⟨72049779729928413843587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 768530983785903080998261 72049779729928413843587)
                ·
                  rfl

theorem cell20_473568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_473568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473568 prefixEnd_473568 := by exact prefixLift 473568
  have htrace : WordTrace (prefixWord ++ tailWord_473568) baseStart_473568 baseEnd_473568 := by
    simpa [prefixWord, tailWord_473568, baseEnd_473568] using wordTrace_append hprefix tailTrace_473568
  have hstable : (prefixWord ++ tailWord_473568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473568).length < 2 ^ (prefixWord ++ tailWord_473568).sum := by decide
  have hdescent : baseEnd_473568 < baseStart_473568 := by decide
  rcases family_descends (prefixWord ++ tailWord_473568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473571 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_473571 : Nat := 118140960795 + 473571 * 2 ^ 59
def prefixEnd_473571 : Nat := 4983230072969 + 3 ^ 40 * 473571 * 2
def baseEnd_473571 : Nat := 216150708471530564430749

theorem tailTrace_473571 : CollatzResearch.WordTrace tailWord_473571 prefixEnd_473571 216150708471530564430749 := by
  unfold tailWord_473571
  simp only [CollatzResearch.WordTrace]
  refine ⟨17272553367340621332764567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11515035578227080888509711 17272553367340621332764567)
  ·
    refine ⟨25908830051010931999146851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17272553367340621332764567 25908830051010931999146851)
    ·
      refine ⟨38863245076516397998720277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25908830051010931999146851 38863245076516397998720277)
      ·
        refine ⟨1821714612961706156190013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38863245076516397998720277 1821714612961706156190013)
        ·
          refine ⟨683142979860639808571255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1821714612961706156190013 683142979860639808571255)
          ·
            refine ⟨1024714469790959712856883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683142979860639808571255 1024714469790959712856883)
            ·
              refine ⟨1537071704686439569285325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024714469790959712856883 1537071704686439569285325)
              ·
                refine ⟨576401889257414838481997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1537071704686439569285325 576401889257414838481997)
                ·
                  refine ⟨216150708471530564430749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576401889257414838481997 216150708471530564430749)
                  ·
                    rfl

theorem cell20_473571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_473571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473571 prefixEnd_473571 := by exact prefixLift 473571
  have htrace : WordTrace (prefixWord ++ tailWord_473571) baseStart_473571 baseEnd_473571 := by
    simpa [prefixWord, tailWord_473571, baseEnd_473571] using wordTrace_append hprefix tailTrace_473571
  have hstable : (prefixWord ++ tailWord_473571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473571).length < 2 ^ (prefixWord ++ tailWord_473571).sum := by decide
  have hdescent : baseEnd_473571 < baseStart_473571 := by decide
  rcases family_descends (prefixWord ++ tailWord_473571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473602 : List Nat := [3, 4, 1, 2, 3, 7]
def baseStart_473602 : Nat := 118140960795 + 473602 * 2 ^ 59
def prefixEnd_473602 : Nat := 4983230072969 + 3 ^ 40 * 473602 * 2
def baseEnd_473602 : Nat := 8006105841341934607307

theorem tailTrace_473602 : CollatzResearch.WordTrace tailWord_473602 prefixEnd_473602 8006105841341934607307 := by
  unfold tailWord_473602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318421007557078406785765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11515789353485542418095373 4318421007557078406785765)
  ·
    refine ⟨809703938916952201272331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4318421007557078406785765 809703938916952201272331)
    ·
      refine ⟨1214555908375428301908497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809703938916952201272331 1214555908375428301908497)
      ·
        refine ⟨910916931281571226431373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1214555908375428301908497 910916931281571226431373)
        ·
          refine ⟨341593849230589209911765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910916931281571226431373 341593849230589209911765)
          ·
            refine ⟨8006105841341934607307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 341593849230589209911765 8006105841341934607307)
            ·
              rfl

theorem cell20_473602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 7].length) (baseStart_473602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473602 prefixEnd_473602 := by exact prefixLift 473602
  have htrace : WordTrace (prefixWord ++ tailWord_473602) baseStart_473602 baseEnd_473602 := by
    simpa [prefixWord, tailWord_473602, baseEnd_473602] using wordTrace_append hprefix tailTrace_473602
  have hstable : (prefixWord ++ tailWord_473602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473602).length < 2 ^ (prefixWord ++ tailWord_473602).sum := by decide
  have hdescent : baseEnd_473602 < baseStart_473602 := by decide
  rcases family_descends (prefixWord ++ tailWord_473602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473612 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 2]
def baseStart_473612 : Nat := 118140960795 + 473612 * 2 ^ 59
def prefixEnd_473612 : Nat := 4983230072969 + 3 ^ 40 * 473612 * 2
def baseEnd_473612 : Nat := 216169421988716644063915

theorem tailTrace_473612 : CollatzResearch.WordTrace tailWord_473612 prefixEnd_473612 216169421988716644063915 := by
  unfold tailWord_473612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637024380096042667503545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11516032506794723556671393 8637024380096042667503545)
  ·
    refine ⟨6477768285072032000627659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8637024380096042667503545 6477768285072032000627659)
    ·
      refine ⟨9716652427608048000941489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6477768285072032000627659 9716652427608048000941489)
      ·
        refine ⟨7287489320706036000706117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9716652427608048000941489 7287489320706036000706117)
        ·
          refine ⟨1366404247632381750132397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7287489320706036000706117 1366404247632381750132397)
          ·
            refine ⟨512401592862143156299649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1366404247632381750132397 512401592862143156299649)
            ·
              refine ⟨384301194646607367224737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512401592862143156299649 384301194646607367224737)
              ·
                refine ⟨288225895984955525418553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384301194646607367224737 288225895984955525418553)
                ·
                  refine ⟨216169421988716644063915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288225895984955525418553 216169421988716644063915)
                  ·
                    rfl

theorem cell20_473612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_473612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473612 prefixEnd_473612 := by exact prefixLift 473612
  have htrace : WordTrace (prefixWord ++ tailWord_473612) baseStart_473612 baseEnd_473612 := by
    simpa [prefixWord, tailWord_473612, baseEnd_473612] using wordTrace_append hprefix tailTrace_473612
  have hstable : (prefixWord ++ tailWord_473612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473612).length < 2 ^ (prefixWord ++ tailWord_473612).sum := by decide
  have hdescent : baseEnd_473612 < baseStart_473612 := by decide
  rcases family_descends (prefixWord ++ tailWord_473612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473640 : List Nat := [2, 1, 5, 2, 1, 2, 3, 4]
def baseStart_473640 : Nat := 118140960795 + 473640 * 2 ^ 59
def prefixEnd_473640 : Nat := 4983230072969 + 3 ^ 40 * 473640 * 2
def baseEnd_473640 : Nat := 72060733983890997043489

theorem tailTrace_473640 : CollatzResearch.WordTrace tailWord_473640 prefixEnd_473640 72060733983890997043489 := by
  unfold tailWord_473640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637535002045323058513187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11516713336060430744684249 8637535002045323058513187)
  ·
    refine ⟨12956302503067984587769781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8637535002045323058513187 12956302503067984587769781)
    ·
      refine ⟨1214653359662623555103417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12956302503067984587769781 1214653359662623555103417)
      ·
        refine ⟨910990019746967666327563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1214653359662623555103417 910990019746967666327563)
        ·
          refine ⟨1366485029620451499491345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910990019746967666327563 1366485029620451499491345)
          ·
            refine ⟨1024863772215338624618509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1366485029620451499491345 1024863772215338624618509)
            ·
              refine ⟨384323914580751984231941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1024863772215338624618509 384323914580751984231941)
              ·
                refine ⟨72060733983890997043489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384323914580751984231941 72060733983890997043489)
                ·
                  rfl

theorem cell20_473640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_473640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473640 prefixEnd_473640 := by exact prefixLift 473640
  have htrace : WordTrace (prefixWord ++ tailWord_473640) baseStart_473640 baseEnd_473640 := by
    simpa [prefixWord, tailWord_473640, baseEnd_473640] using wordTrace_append hprefix tailTrace_473640
  have hstable : (prefixWord ++ tailWord_473640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473640).length < 2 ^ (prefixWord ++ tailWord_473640).sum := by decide
  have hdescent : baseEnd_473640 < baseStart_473640 := by decide
  rcases family_descends (prefixWord ++ tailWord_473640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473651 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_473651 : Nat := 118140960795 + 473651 * 2 ^ 59
def prefixEnd_473651 : Nat := 4983230072969 + 3 ^ 40 * 473651 * 2
def baseEnd_473651 : Nat := 216187222651405841763755

theorem tailTrace_473651 : CollatzResearch.WordTrace tailWord_473651 prefixEnd_473651 216187222651405841763755 := by
  unfold tailWord_473651
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275471207050794995676807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11516980804700529997117871 17275471207050794995676807)
  ·
    refine ⟨25913206810576192493515211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275471207050794995676807 25913206810576192493515211)
    ·
      refine ⟨38869810215864288740272817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25913206810576192493515211 38869810215864288740272817)
      ·
        refine ⟨29152357661898216555204613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38869810215864288740272817 29152357661898216555204613)
        ·
          refine ⟨5466067061605915604100865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29152357661898216555204613 5466067061605915604100865)
          ·
            refine ⟨4099550296204436703075649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5466067061605915604100865 4099550296204436703075649)
            ·
              refine ⟨3074662722153327527306737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099550296204436703075649 3074662722153327527306737)
              ·
                refine ⟨2305997041614995645480053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074662722153327527306737 2305997041614995645480053)
                ·
                  refine ⟨216187222651405841763755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2305997041614995645480053 216187222651405841763755)
                  ·
                    rfl

theorem cell20_473651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_473651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473651 prefixEnd_473651 := by exact prefixLift 473651
  have htrace : WordTrace (prefixWord ++ tailWord_473651) baseStart_473651 baseEnd_473651 := by
    simpa [prefixWord, tailWord_473651, baseEnd_473651] using wordTrace_append hprefix tailTrace_473651
  have hstable : (prefixWord ++ tailWord_473651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473651).length < 2 ^ (prefixWord ++ tailWord_473651).sum := by decide
  have hdescent : baseEnd_473651 < baseStart_473651 := by decide
  rcases family_descends (prefixWord ++ tailWord_473651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473682 : List Nat := [3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_473682 : Nat := 118140960795 + 473682 * 2 ^ 59
def prefixEnd_473682 : Nat := 4983230072969 + 3 ^ 40 * 473682 * 2
def baseEnd_473682 : Nat := 72067123965369170576765

theorem tailTrace_473682 : CollatzResearch.WordTrace tailWord_473682 prefixEnd_473682 72067123965369170576765 := by
  unfold tailWord_473682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319150467484621822513825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11517734579958991526703533 4319150467484621822513825)
  ·
    refine ⟨3239362850613466366885369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4319150467484621822513825 3239362850613466366885369)
    ·
      refine ⟨2429522137960099775164027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3239362850613466366885369 2429522137960099775164027)
      ·
        refine ⟨3644283206940149662746041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429522137960099775164027 3644283206940149662746041)
        ·
          refine ⟨2733212405205112247059531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3644283206940149662746041 2733212405205112247059531)
          ·
            refine ⟨4099818607807668370589297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733212405205112247059531 4099818607807668370589297)
            ·
              refine ⟨3074863955855751277941973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099818607807668370589297 3074863955855751277941973)
              ·
                refine ⟨72067123965369170576765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3074863955855751277941973 72067123965369170576765)
                ·
                  rfl

theorem cell20_473682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_473682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473682 prefixEnd_473682 := by exact prefixLift 473682
  have htrace : WordTrace (prefixWord ++ tailWord_473682) baseStart_473682 baseEnd_473682 := by
    simpa [prefixWord, tailWord_473682, baseEnd_473682] using wordTrace_append hprefix tailTrace_473682
  have hstable : (prefixWord ++ tailWord_473682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473682).length < 2 ^ (prefixWord ++ tailWord_473682).sum := by decide
  have hdescent : baseEnd_473682 < baseStart_473682 := by decide
  rcases family_descends (prefixWord ++ tailWord_473682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473709 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 2]
def baseStart_473709 : Nat := 118140960795 + 473709 * 2 ^ 59
def prefixEnd_473709 : Nat := 4983230072969 + 3 ^ 40 * 473709 * 2
def baseEnd_473709 : Nat := 216213695431815417830185

theorem tailTrace_473709 : CollatzResearch.WordTrace tailWord_473709 prefixEnd_473709 216213695431815417830185 := by
  unfold tailWord_473709
  simp only [CollatzResearch.WordTrace]
  refine ⟨17277586640840670901288181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11518391093893780600858787 17277586640840670901288181)
  ·
    refine ⟨1619773747578812896995767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17277586640840670901288181 1619773747578812896995767)
    ·
      refine ⟨2429660621368219345493651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619773747578812896995767 2429660621368219345493651)
      ·
        refine ⟨3644490932052329018240477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429660621368219345493651 3644490932052329018240477)
        ·
          refine ⟨1366684099519623381840179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3644490932052329018240477 1366684099519623381840179)
          ·
            refine ⟨2050026149279435072760269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366684099519623381840179 2050026149279435072760269)
            ·
              refine ⟨768759805979788152285101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2050026149279435072760269 768759805979788152285101)
              ·
                refine ⟨288284927242420557106913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 768759805979788152285101 288284927242420557106913)
                ·
                  refine ⟨216213695431815417830185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288284927242420557106913 216213695431815417830185)
                  ·
                    rfl

theorem cell20_473709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_473709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473709 prefixEnd_473709 := by exact prefixLift 473709
  have htrace : WordTrace (prefixWord ++ tailWord_473709) baseStart_473709 baseEnd_473709 := by
    simpa [prefixWord, tailWord_473709, baseEnd_473709] using wordTrace_append hprefix tailTrace_473709
  have hstable : (prefixWord ++ tailWord_473709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473709).length < 2 ^ (prefixWord ++ tailWord_473709).sum := by decide
  have hdescent : baseEnd_473709 < baseStart_473709 := by decide
  rcases family_descends (prefixWord ++ tailWord_473709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473779 : List Nat := [1, 1, 1, 2, 3, 12]
def baseStart_473779 : Nat := 118140960795 + 473779 * 2 ^ 59
def prefixEnd_473779 : Nat := 4983230072969 + 3 ^ 40 * 473779 * 2
def baseEnd_473779 : Nat := 8009097975526158722095

theorem tailTrace_473779 : CollatzResearch.WordTrace tailWord_473779 prefixEnd_473779 8009097975526158722095 := by
  unfold tailWord_473779
  simp only [CollatzResearch.WordTrace]
  refine ⟨17280139750587072856336391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11520093167058048570890927 17280139750587072856336391)
  ·
    refine ⟨25920209625880609284504587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17280139750587072856336391 25920209625880609284504587)
    ·
      refine ⟨38880314438820913926756881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25920209625880609284504587 38880314438820913926756881)
      ·
        refine ⟨29160235829115685445067661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38880314438820913926756881 29160235829115685445067661)
        ·
          refine ⟨10935088435918382041900373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29160235829115685445067661 10935088435918382041900373)
          ·
            refine ⟨8009097975526158722095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10935088435918382041900373 8009097975526158722095)
            ·
              rfl

theorem cell20_473779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 12].length) (baseStart_473779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473779 prefixEnd_473779 := by exact prefixLift 473779
  have htrace : WordTrace (prefixWord ++ tailWord_473779) baseStart_473779 baseEnd_473779 := by
    simpa [prefixWord, tailWord_473779, baseEnd_473779] using wordTrace_append hprefix tailTrace_473779
  have hstable : (prefixWord ++ tailWord_473779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473779).length < 2 ^ (prefixWord ++ tailWord_473779).sum := by decide
  have hdescent : baseEnd_473779 < baseStart_473779 := by decide
  rcases family_descends (prefixWord ++ tailWord_473779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473841 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_473841 : Nat := 118140960795 + 473841 * 2 ^ 59
def prefixEnd_473841 : Nat := 4983230072969 + 3 ^ 40 * 473841 * 2
def baseEnd_473841 : Nat := 216273943828609625429645

theorem tailTrace_473841 : CollatzResearch.WordTrace tailWord_473841 prefixEnd_473841 216273943828609625429645 := by
  unfold tailWord_473841
  simp only [CollatzResearch.WordTrace]
  refine ⟨17282401076362457445093377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11521600717574971630062251 17282401076362457445093377)
  ·
    refine ⟨12961800807271843083820033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17282401076362457445093377 12961800807271843083820033)
    ·
      refine ⟨9721350605453882312865025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12961800807271843083820033 9721350605453882312865025)
      ·
        refine ⟨7291012954090411734648769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9721350605453882312865025 7291012954090411734648769)
        ·
          refine ⟨5468259715567808800986577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7291012954090411734648769 5468259715567808800986577)
          ·
            refine ⟨4101194786675856600739933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468259715567808800986577 4101194786675856600739933)
            ·
              refine ⟨1537948045003446225277475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4101194786675856600739933 1537948045003446225277475)
              ·
                refine ⟨2306922067505169337916213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537948045003446225277475 2306922067505169337916213)
                ·
                  refine ⟨216273943828609625429645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2306922067505169337916213 216273943828609625429645)
                  ·
                    rfl

theorem cell20_473841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_473841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473841 prefixEnd_473841 := by exact prefixLift 473841
  have htrace : WordTrace (prefixWord ++ tailWord_473841) baseStart_473841 baseEnd_473841 := by
    simpa [prefixWord, tailWord_473841, baseEnd_473841] using wordTrace_append hprefix tailTrace_473841
  have hstable : (prefixWord ++ tailWord_473841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473841).length < 2 ^ (prefixWord ++ tailWord_473841).sum := by decide
  have hdescent : baseEnd_473841 < baseStart_473841 := by decide
  rcases family_descends (prefixWord ++ tailWord_473841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473854 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_473854 : Nat := 118140960795 + 473854 * 2 ^ 59
def prefixEnd_473854 : Nat := 4983230072969 + 3 ^ 40 * 473854 * 2
def baseEnd_473854 : Nat := 216279877382839357996259

theorem tailTrace_473854 : CollatzResearch.WordTrace tailWord_473854 prefixEnd_473854 216279877382839357996259 := by
  unfold tailWord_473854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160359403164420083164577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11521916816876907110211077 2160359403164420083164577)
  ·
    refine ⟨1620269552373315062373433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2160359403164420083164577 1620269552373315062373433)
    ·
      refine ⟨1215202164279986296780075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1620269552373315062373433 1215202164279986296780075)
      ·
        refine ⟨1822803246419979445170113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215202164279986296780075 1822803246419979445170113)
        ·
          refine ⟨1367102434814984583877585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822803246419979445170113 1367102434814984583877585)
          ·
            refine ⟨1025326826111238437908189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367102434814984583877585 1025326826111238437908189)
            ·
              refine ⟨384497559791714414215571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1025326826111238437908189 384497559791714414215571)
              ·
                refine ⟨576746339687571621323357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384497559791714414215571 576746339687571621323357)
                ·
                  refine ⟨216279877382839357996259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576746339687571621323357 216279877382839357996259)
                  ·
                    rfl

theorem cell20_473854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_473854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473854 prefixEnd_473854 := by exact prefixLift 473854
  have htrace : WordTrace (prefixWord ++ tailWord_473854) baseStart_473854 baseEnd_473854 := by
    simpa [prefixWord, tailWord_473854, baseEnd_473854] using wordTrace_append hprefix tailTrace_473854
  have hstable : (prefixWord ++ tailWord_473854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473854).length < 2 ^ (prefixWord ++ tailWord_473854).sum := by decide
  have hdescent : baseEnd_473854 < baseStart_473854 := by decide
  rcases family_descends (prefixWord ++ tailWord_473854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473855 : List Nat := [1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_473855 : Nat := 118140960795 + 473855 * 2 ^ 59
def prefixEnd_473855 : Nat := 4983230072969 + 3 ^ 40 * 473855 * 2
def baseEnd_473855 : Nat := 72093444603362599654307

theorem tailTrace_473855 : CollatzResearch.WordTrace tailWord_473855 prefixEnd_473855 72093444603362599654307 := by
  unfold tailWord_473855
  simp only [CollatzResearch.WordTrace]
  refine ⟨17282911698311737836103019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11521941132207825224068679 17282911698311737836103019)
  ·
    refine ⟨25924367547467606754154529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17282911698311737836103019 25924367547467606754154529)
    ·
      refine ⟨19443275660600705065615897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25924367547467606754154529 19443275660600705065615897)
      ·
        refine ⟨14582456745450528799211923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19443275660600705065615897 14582456745450528799211923)
        ·
          refine ⟨21873685118175793198817885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14582456745450528799211923 21873685118175793198817885)
          ·
            refine ⟨8202631919315922449556707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21873685118175793198817885 8202631919315922449556707)
            ·
              refine ⟨12303947878973883674335061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202631919315922449556707 12303947878973883674335061)
              ·
                refine ⟨72093444603362599654307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12303947878973883674335061 72093444603362599654307)
                ·
                  rfl

theorem cell20_473855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_473855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473855 prefixEnd_473855 := by exact prefixLift 473855
  have htrace : WordTrace (prefixWord ++ tailWord_473855) baseStart_473855 baseEnd_473855 := by
    simpa [prefixWord, tailWord_473855, baseEnd_473855] using wordTrace_append hprefix tailTrace_473855
  have hstable : (prefixWord ++ tailWord_473855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473855).length < 2 ^ (prefixWord ++ tailWord_473855).sum := by decide
  have hdescent : baseEnd_473855 < baseStart_473855 := by decide
  rcases family_descends (prefixWord ++ tailWord_473855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473896 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_473896 : Nat := 118140960795 + 473896 * 2 ^ 59
def prefixEnd_473896 : Nat := 4983230072969 + 3 ^ 40 * 473896 * 2
def baseEnd_473896 : Nat := 216299047327273878596087

theorem tailTrace_473896 : CollatzResearch.WordTrace tailWord_473896 prefixEnd_473896 216299047327273878596087 := by
  unfold tailWord_473896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8642203545581600919172771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11522938060775467892230361 8642203545581600919172771)
  ·
    refine ⟨12963305318372401378759157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8642203545581600919172771 12963305318372401378759157)
    ·
      refine ⟨1215309873597412629258671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12963305318372401378759157 1215309873597412629258671)
      ·
        refine ⟨1822964810396118943888007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215309873597412629258671 1822964810396118943888007)
        ·
          refine ⟨2734447215594178415832011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822964810396118943888007 2734447215594178415832011)
          ·
            refine ⟨4101670823391267623748017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734447215594178415832011 4101670823391267623748017)
            ·
              refine ⟨3076253117543450717811013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101670823391267623748017 3076253117543450717811013)
              ·
                refine ⟨576797459539397009589565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3076253117543450717811013 576797459539397009589565)
                ·
                  refine ⟨216299047327273878596087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576797459539397009589565 216299047327273878596087)
                  ·
                    rfl

theorem cell20_473896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_473896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473896 prefixEnd_473896 := by exact prefixLift 473896
  have htrace : WordTrace (prefixWord ++ tailWord_473896) baseStart_473896 baseEnd_473896 := by
    simpa [prefixWord, tailWord_473896, baseEnd_473896] using wordTrace_append hprefix tailTrace_473896
  have hstable : (prefixWord ++ tailWord_473896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473896).length < 2 ^ (prefixWord ++ tailWord_473896).sum := by decide
  have hdescent : baseEnd_473896 < baseStart_473896 := by decide
  rcases family_descends (prefixWord ++ tailWord_473896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_473948 : List Nat := [2, 2, 4, 2, 1, 9]
def baseStart_473948 : Nat := 118140960795 + 473948 * 2 ^ 59
def prefixEnd_473948 : Nat := 4983230072969 + 3 ^ 40 * 473948 * 2
def baseEnd_473948 : Nat := 8011954872007141068983

theorem tailTrace_473948 : CollatzResearch.WordTrace tailWord_473948 prefixEnd_473948 8011954872007141068983 := by
  unfold tailWord_473948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643151843487407359619249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11524202457983209812825665 8643151843487407359619249)
  ·
    refine ⟨6482363882615555519714437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8643151843487407359619249 6482363882615555519714437)
    ·
      refine ⟨1215443227990416659946457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6482363882615555519714437 1215443227990416659946457)
      ·
        refine ⟨911582420992812494959843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1215443227990416659946457 911582420992812494959843)
        ·
          refine ⟨1367373631489218742439765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911582420992812494959843 1367373631489218742439765)
          ·
            refine ⟨8011954872007141068983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1367373631489218742439765 8011954872007141068983)
            ·
              rfl

theorem cell20_473948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 9].length) (baseStart_473948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_473948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_473948 prefixEnd_473948 := by exact prefixLift 473948
  have htrace : WordTrace (prefixWord ++ tailWord_473948) baseStart_473948 baseEnd_473948 := by
    simpa [prefixWord, tailWord_473948, baseEnd_473948] using wordTrace_append hprefix tailTrace_473948
  have hstable : (prefixWord ++ tailWord_473948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_473948).length < 2 ^ (prefixWord ++ tailWord_473948).sum := by decide
  have hdescent : baseEnd_473948 < baseStart_473948 := by decide
  rcases family_descends (prefixWord ++ tailWord_473948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474006 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_474006 : Nat := 118140960795 + 474006 * 2 ^ 59
def prefixEnd_474006 : Nat := 4983230072969 + 3 ^ 40 * 474006 * 2
def baseEnd_474006 : Nat := 216349254324602384928971

theorem tailTrace_474006 : CollatzResearch.WordTrace tailWord_474006 prefixEnd_474006 216349254324602384928971 := by
  unfold tailWord_474006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080526195047793164053117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11525612747176460416566581 1080526195047793164053117)
  ·
    refine ⟨405197323142922436519919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1080526195047793164053117 405197323142922436519919)
    ·
      refine ⟨607795984714383654779879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405197323142922436519919 607795984714383654779879)
      ·
        refine ⟨911693977071575482169819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607795984714383654779879 911693977071575482169819)
        ·
          refine ⟨1367540965607363223254729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911693977071575482169819 1367540965607363223254729)
          ·
            refine ⟨1025655724205522417441047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367540965607363223254729 1025655724205522417441047)
            ·
              refine ⟨1538483586308283626161571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025655724205522417441047 1538483586308283626161571)
              ·
                refine ⟨2307725379462425439242357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538483586308283626161571 2307725379462425439242357)
                ·
                  refine ⟨216349254324602384928971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307725379462425439242357 216349254324602384928971)
                  ·
                    rfl

theorem cell20_474006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_474006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474006 prefixEnd_474006 := by exact prefixLift 474006
  have htrace : WordTrace (prefixWord ++ tailWord_474006) baseStart_474006 baseEnd_474006 := by
    simpa [prefixWord, tailWord_474006, baseEnd_474006] using wordTrace_append hprefix tailTrace_474006
  have hstable : (prefixWord ++ tailWord_474006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474006).length < 2 ^ (prefixWord ++ tailWord_474006).sum := by decide
  have hdescent : baseEnd_474006 < baseStart_474006 := by decide
  rcases family_descends (prefixWord ++ tailWord_474006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474007 : List Nat := [1, 1, 3, 3, 1, 2, 9]
def baseStart_474007 : Nat := 118140960795 + 474007 * 2 ^ 59
def prefixEnd_474007 : Nat := 4983230072969 + 3 ^ 40 * 474007 * 2
def baseEnd_474007 : Nat := 24038856750205647321737

theorem tailTrace_474007 : CollatzResearch.WordTrace tailWord_474007 prefixEnd_474007 24038856750205647321737 := by
  unfold tailWord_474007
  simp only [CollatzResearch.WordTrace]
  refine ⟨17288455593761067795636275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11525637062507378530424183 17288455593761067795636275)
  ·
    refine ⟨25932683390641601693454413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17288455593761067795636275 25932683390641601693454413)
    ·
      refine ⟨9724756271490600635045405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25932683390641601693454413 9724756271490600635045405)
      ·
        refine ⟨3646783601808975238142027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9724756271490600635045405 3646783601808975238142027)
        ·
          refine ⟨5470175402713462857213041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646783601808975238142027 5470175402713462857213041)
          ·
            refine ⟨4102631552035097142909781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5470175402713462857213041 4102631552035097142909781)
            ·
              refine ⟨24038856750205647321737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4102631552035097142909781 24038856750205647321737)
              ·
                rfl

theorem cell20_474007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_474007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474007 prefixEnd_474007 := by exact prefixLift 474007
  have htrace : WordTrace (prefixWord ++ tailWord_474007) baseStart_474007 baseEnd_474007 := by
    simpa [prefixWord, tailWord_474007, baseEnd_474007] using wordTrace_append hprefix tailTrace_474007
  have hstable : (prefixWord ++ tailWord_474007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474007).length < 2 ^ (prefixWord ++ tailWord_474007).sum := by decide
  have hdescent : baseEnd_474007 < baseStart_474007 := by decide
  rcases family_descends (prefixWord ++ tailWord_474007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474010 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_474010 : Nat := 118140960795 + 474010 * 2 ^ 59
def prefixEnd_474010 : Nat := 4983230072969 + 3 ^ 40 * 474010 * 2
def baseEnd_474010 : Nat := 216351080033596148795621

theorem tailTrace_474010 : CollatzResearch.WordTrace tailWord_474010 prefixEnd_474010 216351080033596148795621 := by
  unfold tailWord_474010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322141253187549826998871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11525710008500132871996989 4322141253187549826998871)
  ·
    refine ⟨6483211879781324740498307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322141253187549826998871 6483211879781324740498307)
    ·
      refine ⟨9724817819671987110747461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6483211879781324740498307 9724817819671987110747461)
      ·
        refine ⟨1823403341188497583265149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9724817819671987110747461 1823403341188497583265149)
        ·
          refine ⟨683776252945686593724431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1823403341188497583265149 683776252945686593724431)
          ·
            refine ⟨1025664379418529890586647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683776252945686593724431 1025664379418529890586647)
            ·
              refine ⟨1538496569127794835879971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025664379418529890586647 1538496569127794835879971)
              ·
                refine ⟨2307744853691692253819957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538496569127794835879971 2307744853691692253819957)
                ·
                  refine ⟨216351080033596148795621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2307744853691692253819957 216351080033596148795621)
                  ·
                    rfl

theorem cell20_474010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_474010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474010 prefixEnd_474010 := by exact prefixLift 474010
  have htrace : WordTrace (prefixWord ++ tailWord_474010) baseStart_474010 baseEnd_474010 := by
    simpa [prefixWord, tailWord_474010, baseEnd_474010] using wordTrace_append hprefix tailTrace_474010
  have hstable : (prefixWord ++ tailWord_474010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474010).length < 2 ^ (prefixWord ++ tailWord_474010).sum := by decide
  have hdescent : baseEnd_474010 < baseStart_474010 := by decide
  rcases family_descends (prefixWord ++ tailWord_474010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474017 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_474017 : Nat := 118140960795 + 474017 * 2 ^ 59
def prefixEnd_474017 : Nat := 4983230072969 + 3 ^ 40 * 474017 * 2
def baseEnd_474017 : Nat := 216354275024335235562259

theorem tailTrace_474017 : CollatzResearch.WordTrace tailWord_474017 prefixEnd_474017 216354275024335235562259 := by
  unfold tailWord_474017
  simp only [CollatzResearch.WordTrace]
  refine ⟨17288820323724839503500305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11525880215816559669000203 17288820323724839503500305)
  ·
    refine ⟨12966615242793629627625229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17288820323724839503500305 12966615242793629627625229)
    ·
      refine ⟨4862480716047611110359461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12966615242793629627625229 4862480716047611110359461)
      ·
        refine ⟨911715134258927083192399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4862480716047611110359461 911715134258927083192399)
        ·
          refine ⟨1367572701388390624788599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911715134258927083192399 1367572701388390624788599)
          ·
            refine ⟨2051359052082585937182899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367572701388390624788599 2051359052082585937182899)
            ·
              refine ⟨3077038578123878905774349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051359052082585937182899 3077038578123878905774349)
              ·
                refine ⟨1153889466796454589665381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3077038578123878905774349 1153889466796454589665381)
                ·
                  refine ⟨216354275024335235562259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153889466796454589665381 216354275024335235562259)
                  ·
                    rfl

theorem cell20_474017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_474017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474017 prefixEnd_474017 := by exact prefixLift 474017
  have htrace : WordTrace (prefixWord ++ tailWord_474017) baseStart_474017 baseEnd_474017 := by
    simpa [prefixWord, tailWord_474017, baseEnd_474017] using wordTrace_append hprefix tailTrace_474017
  have hstable : (prefixWord ++ tailWord_474017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474017).length < 2 ^ (prefixWord ++ tailWord_474017).sum := by decide
  have hdescent : baseEnd_474017 < baseStart_474017 := by decide
  rcases family_descends (prefixWord ++ tailWord_474017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474041 : List Nat := [1, 2, 1, 4, 2, 4, 2, 4]
def baseStart_474041 : Nat := 118140960795 + 474041 * 2 ^ 59
def prefixEnd_474041 : Nat := 4983230072969 + 3 ^ 40 * 474041 * 2
def baseEnd_474041 : Nat := 72121743092765939587387

theorem tailTrace_474041 : CollatzResearch.WordTrace tailWord_474041 prefixEnd_474041 72121743092765939587387 := by
  unfold tailWord_474041
  simp only [CollatzResearch.WordTrace]
  refine ⟨17289695675637891602373977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11526463783758594401582651 17289695675637891602373977)
  ·
    refine ⟨12967271756728418701780483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17289695675637891602373977 12967271756728418701780483)
    ·
      refine ⟨19450907635092628052670725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12967271756728418701780483 19450907635092628052670725)
      ·
        refine ⟨3647045181579867759875761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19450907635092628052670725 3647045181579867759875761)
        ·
          refine ⟨2735283886184900819906821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3647045181579867759875761 2735283886184900819906821)
          ·
            refine ⟨512865728659668903732529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2735283886184900819906821 512865728659668903732529)
            ·
              refine ⟨384649296494751677799397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512865728659668903732529 384649296494751677799397)
              ·
                refine ⟨72121743092765939587387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384649296494751677799397 72121743092765939587387)
                ·
                  rfl

theorem cell20_474041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_474041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474041 prefixEnd_474041 := by exact prefixLift 474041
  have htrace : WordTrace (prefixWord ++ tailWord_474041) baseStart_474041 baseEnd_474041 := by
    simpa [prefixWord, tailWord_474041, baseEnd_474041] using wordTrace_append hprefix tailTrace_474041
  have hstable : (prefixWord ++ tailWord_474041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474041).length < 2 ^ (prefixWord ++ tailWord_474041).sum := by decide
  have hdescent : baseEnd_474041 < baseStart_474041 := by decide
  rcases family_descends (prefixWord ++ tailWord_474041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474054 : List Nat := [6, 1, 3, 1, 1, 2, 6]
def baseStart_474054 : Nat := 118140960795 + 474054 * 2 ^ 59
def prefixEnd_474054 : Nat := 4983230072969 + 3 ^ 40 * 474054 * 2
def baseEnd_474054 : Nat := 24041240314725283480975

theorem tailTrace_474054 : CollatzResearch.WordTrace tailWord_474054 prefixEnd_474054 24041240314725283480975 := by
  unfold tailWord_474054
  simp only [CollatzResearch.WordTrace]
  refine ⟨540317807018462338206163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11526779883060529881731477 540317807018462338206163)
  ·
    refine ⟨810476710527693507309245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540317807018462338206163 810476710527693507309245)
    ·
      refine ⟨303928766447885065240967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 810476710527693507309245 303928766447885065240967)
      ·
        refine ⟨455893149671827597861451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303928766447885065240967 455893149671827597861451)
        ·
          refine ⟨683839724507741396792177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455893149671827597861451 683839724507741396792177)
          ·
            refine ⟨512879793380806047594133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683839724507741396792177 512879793380806047594133)
            ·
              refine ⟨24041240314725283480975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512879793380806047594133 24041240314725283480975)
              ·
                rfl

theorem cell20_474054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 6].length) (baseStart_474054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474054 prefixEnd_474054 := by exact prefixLift 474054
  have htrace : WordTrace (prefixWord ++ tailWord_474054) baseStart_474054 baseEnd_474054 := by
    simpa [prefixWord, tailWord_474054, baseEnd_474054] using wordTrace_append hprefix tailTrace_474054
  have hstable : (prefixWord ++ tailWord_474054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474054).length < 2 ^ (prefixWord ++ tailWord_474054).sum := by decide
  have hdescent : baseEnd_474054 < baseStart_474054 := by decide
  rcases family_descends (prefixWord ++ tailWord_474054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474062 : List Nat := [4, 1, 1, 1, 2, 5, 6]
def baseStart_474062 : Nat := 118140960795 + 474062 * 2 ^ 59
def prefixEnd_474062 : Nat := 4983230072969 + 3 ^ 40 * 474062 * 2
def baseEnd_474062 : Nat := 24041646027835008784675

theorem tailTrace_474062 : CollatzResearch.WordTrace tailWord_474062 prefixEnd_474062 24041646027835008784675 := by
  unfold tailWord_474062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161307701070226523611055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11526974405707874792592293 2161307701070226523611055)
  ·
    refine ⟨3241961551605339785416583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2161307701070226523611055 3241961551605339785416583)
    ·
      refine ⟨4862942327408009678124875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3241961551605339785416583 4862942327408009678124875)
      ·
        refine ⟨7294413491112014517187313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862942327408009678124875 7294413491112014517187313)
        ·
          refine ⟨5470810118334010887890485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7294413491112014517187313 5470810118334010887890485)
          ·
            refine ⟨512888448593813520739733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5470810118334010887890485 512888448593813520739733)
            ·
              refine ⟨24041646027835008784675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512888448593813520739733 24041646027835008784675)
              ·
                rfl

theorem cell20_474062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 6].length) (baseStart_474062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474062 prefixEnd_474062 := by exact prefixLift 474062
  have htrace : WordTrace (prefixWord ++ tailWord_474062) baseStart_474062 baseEnd_474062 := by
    simpa [prefixWord, tailWord_474062, baseEnd_474062] using wordTrace_append hprefix tailTrace_474062
  have hstable : (prefixWord ++ tailWord_474062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474062).length < 2 ^ (prefixWord ++ tailWord_474062).sum := by decide
  have hdescent : baseEnd_474062 < baseStart_474062 := by decide
  rcases family_descends (prefixWord ++ tailWord_474062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474082 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_474082 : Nat := 118140960795 + 474082 * 2 ^ 59
def prefixEnd_474082 : Nat := 4983230072969 + 3 ^ 40 * 474082 * 2
def baseEnd_474082 : Nat := 216383942795483898395327

theorem tailTrace_474082 : CollatzResearch.WordTrace tailWord_474082 prefixEnd_474082 216383942795483898395327 := by
  unfold tailWord_474082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322797767122338901154125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11527460712326237069744333 4322797767122338901154125)
  ·
    refine ⟨1621049162670877087932797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4322797767122338901154125 1621049162670877087932797)
    ·
      refine ⟨607893436001578907974799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1621049162670877087932797 607893436001578907974799)
      ·
        refine ⟨911840154002368361962199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607893436001578907974799 911840154002368361962199)
        ·
          refine ⟨1367760231003552542943299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911840154002368361962199 1367760231003552542943299)
          ·
            refine ⟨2051640346505328814414949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367760231003552542943299 2051640346505328814414949)
            ·
              refine ⟨384682564969749152702803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2051640346505328814414949 384682564969749152702803)
              ·
                refine ⟨577023847454623729054205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384682564969749152702803 577023847454623729054205)
                ·
                  refine ⟨216383942795483898395327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577023847454623729054205 216383942795483898395327)
                  ·
                    rfl

theorem cell20_474082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_474082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474082 prefixEnd_474082 := by exact prefixLift 474082
  have htrace : WordTrace (prefixWord ++ tailWord_474082) baseStart_474082 baseEnd_474082 := by
    simpa [prefixWord, tailWord_474082, baseEnd_474082] using wordTrace_append hprefix tailTrace_474082
  have hstable : (prefixWord ++ tailWord_474082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474082).length < 2 ^ (prefixWord ++ tailWord_474082).sum := by decide
  have hdescent : baseEnd_474082 < baseStart_474082 := by decide
  rcases family_descends (prefixWord ++ tailWord_474082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474124 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_474124 : Nat := 118140960795 + 474124 * 2 ^ 59
def prefixEnd_474124 : Nat := 4983230072969 + 3 ^ 40 * 474124 * 2
def baseEnd_474124 : Nat := 216403112739918418995155

theorem tailTrace_474124 : CollatzResearch.WordTrace tailWord_474124 prefixEnd_474124 216403112739918418995155 := by
  unfold tailWord_474124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646361467168598388822713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11528481956224797851763617 8646361467168598388822713)
  ·
    refine ⟨6484771100376448791617035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8646361467168598388822713 6484771100376448791617035)
    ·
      refine ⟨9727156650564673187425553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484771100376448791617035 9727156650564673187425553)
      ·
        refine ⟨7295367487923504890569165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9727156650564673187425553 7295367487923504890569165)
        ·
          refine ⟨2735762807971314333963437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7295367487923504890569165 2735762807971314333963437)
          ·
            refine ⟨1025911052989242875236289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2735762807971314333963437 1025911052989242875236289)
            ·
              refine ⟨769433289741932156427217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025911052989242875236289 769433289741932156427217)
              ·
                refine ⟨577074967306449117320413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769433289741932156427217 577074967306449117320413)
                ·
                  refine ⟨216403112739918418995155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577074967306449117320413 216403112739918418995155)
                  ·
                    rfl

theorem cell20_474124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_474124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474124 prefixEnd_474124 := by exact prefixLift 474124
  have htrace : WordTrace (prefixWord ++ tailWord_474124) baseStart_474124 baseEnd_474124 := by
    simpa [prefixWord, tailWord_474124, baseEnd_474124] using wordTrace_append hprefix tailTrace_474124
  have hstable : (prefixWord ++ tailWord_474124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474124).length < 2 ^ (prefixWord ++ tailWord_474124).sum := by decide
  have hdescent : baseEnd_474124 < baseStart_474124 := by decide
  rcases family_descends (prefixWord ++ tailWord_474124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474130 : List Nat := [3, 2, 5, 1, 2, 1, 1, 5]
def baseStart_474130 : Nat := 118140960795 + 474130 * 2 ^ 59
def prefixEnd_474130 : Nat := 4983230072969 + 3 ^ 40 * 474130 * 2
def baseEnd_474130 : Nat := 72135283767803021598377

theorem tailTrace_474130 : CollatzResearch.WordTrace tailWord_474130 prefixEnd_474130 72135283767803021598377 := by
  unfold tailWord_474130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323235443078864950590961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11528627848210306534909229 4323235443078864950590961)
  ·
    refine ⟨3242426582309148712943221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4323235443078864950590961 3242426582309148712943221)
    ·
      refine ⟨303977492091482691838427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3242426582309148712943221 303977492091482691838427)
      ·
        refine ⟨455966238137224037757641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303977492091482691838427 455966238137224037757641)
        ·
          refine ⟨341974678602918028318231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455966238137224037757641 341974678602918028318231)
          ·
            refine ⟨512962017904377042477347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341974678602918028318231 512962017904377042477347)
            ·
              refine ⟨769443026856565563716021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512962017904377042477347 769443026856565563716021)
              ·
                refine ⟨72135283767803021598377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 769443026856565563716021 72135283767803021598377)
                ·
                  rfl

theorem cell20_474130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_474130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474130 prefixEnd_474130 := by exact prefixLift 474130
  have htrace : WordTrace (prefixWord ++ tailWord_474130) baseStart_474130 baseEnd_474130 := by
    simpa [prefixWord, tailWord_474130, baseEnd_474130] using wordTrace_append hprefix tailTrace_474130
  have hstable : (prefixWord ++ tailWord_474130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474130).length < 2 ^ (prefixWord ++ tailWord_474130).sum := by decide
  have hdescent : baseEnd_474130 < baseStart_474130 := by decide
  rcases family_descends (prefixWord ++ tailWord_474130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474183 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_474183 : Nat := 118140960795 + 474183 * 2 ^ 59
def prefixEnd_474183 : Nat := 4983230072969 + 3 ^ 40 * 474183 * 2
def baseEnd_474183 : Nat := 216430041947576436028247

theorem tailTrace_474183 : CollatzResearch.WordTrace tailWord_474183 prefixEnd_474183 216430041947576436028247 := by
  unfold tailWord_474183
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294874841123449854043203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11529916560748966569362135 17294874841123449854043203)
  ·
    refine ⟨25942312261685174781064805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17294874841123449854043203 25942312261685174781064805)
    ·
      refine ⟨4864183549065970271449651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25942312261685174781064805 4864183549065970271449651)
      ·
        refine ⟨7296275323598955407174477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864183549065970271449651 7296275323598955407174477)
        ·
          refine ⟨2736103246349608277690429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7296275323598955407174477 2736103246349608277690429)
          ·
            refine ⟨1026038717381103104133911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2736103246349608277690429 1026038717381103104133911)
            ·
              refine ⟨1539058076071654656200867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026038717381103104133911 1539058076071654656200867)
              ·
                refine ⟨2308587114107481984301301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539058076071654656200867 2308587114107481984301301)
                ·
                  refine ⟨216430041947576436028247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308587114107481984301301 216430041947576436028247)
                  ·
                    rfl

theorem cell20_474183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_474183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474183 prefixEnd_474183 := by exact prefixLift 474183
  have htrace : WordTrace (prefixWord ++ tailWord_474183) baseStart_474183 baseEnd_474183 := by
    simpa [prefixWord, tailWord_474183, baseEnd_474183] using wordTrace_append hprefix tailTrace_474183
  have hstable : (prefixWord ++ tailWord_474183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474183).length < 2 ^ (prefixWord ++ tailWord_474183).sum := by decide
  have hdescent : baseEnd_474183 < baseStart_474183 := by decide
  rcases family_descends (prefixWord ++ tailWord_474183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474197 : List Nat := [1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_474197 : Nat := 118140960795 + 474197 * 2 ^ 59
def prefixEnd_474197 : Nat := 4983230072969 + 3 ^ 40 * 474197 * 2
def baseEnd_474197 : Nat := 72145477309684869853841

theorem tailTrace_474197 : CollatzResearch.WordTrace tailWord_474197 prefixEnd_474197 72145477309684869853841 := by
  unfold tailWord_474197
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295385463072730245052845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11530256975381820163368563 17295385463072730245052845)
  ·
    refine ⟨6485769548652273841894817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17295385463072730245052845 6485769548652273841894817)
    ·
      refine ⟨4864327161489205381421113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6485769548652273841894817 4864327161489205381421113)
      ·
        refine ⟨3648245371116904036065835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4864327161489205381421113 3648245371116904036065835)
        ·
          refine ⟨5472368056675356054098753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648245371116904036065835 5472368056675356054098753)
          ·
            refine ⟨4104276042506517040574065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472368056675356054098753 4104276042506517040574065)
            ·
              refine ⟨3078207031879887780430549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4104276042506517040574065 3078207031879887780430549)
              ·
                refine ⟨72145477309684869853841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3078207031879887780430549 72145477309684869853841)
                ·
                  rfl

theorem cell20_474197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_474197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474197 prefixEnd_474197 := by exact prefixLift 474197
  have htrace : WordTrace (prefixWord ++ tailWord_474197) baseStart_474197 baseEnd_474197 := by
    simpa [prefixWord, tailWord_474197, baseEnd_474197] using wordTrace_append hprefix tailTrace_474197
  have hstable : (prefixWord ++ tailWord_474197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474197).length < 2 ^ (prefixWord ++ tailWord_474197).sum := by decide
  have hdescent : baseEnd_474197 < baseStart_474197 := by decide
  rcases family_descends (prefixWord ++ tailWord_474197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474200 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_474200 : Nat := 118140960795 + 474200 * 2 ^ 59
def prefixEnd_474200 : Nat := 4983230072969 + 3 ^ 40 * 474200 * 2
def baseEnd_474200 : Nat := 216437801210799932461511

theorem tailTrace_474200 : CollatzResearch.WordTrace tailWord_474200 prefixEnd_474200 216437801210799932461511 := by
  unfold tailWord_474200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8647747441030930878706027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11530329921374574504941369 8647747441030930878706027)
  ·
    refine ⟨12971621161546396318059041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8647747441030930878706027 12971621161546396318059041)
    ·
      refine ⟨9728715871159797238544281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12971621161546396318059041 9728715871159797238544281)
      ·
        refine ⟨7296536903369847928908211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9728715871159797238544281 7296536903369847928908211)
        ·
          refine ⟨10944805355054771893362317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296536903369847928908211 10944805355054771893362317)
          ·
            refine ⟨4104302008145539460010869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10944805355054771893362317 4104302008145539460010869)
            ·
              refine ⟨384778313263644324376019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4104302008145539460010869 384778313263644324376019)
              ·
                refine ⟨577167469895466486564029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384778313263644324376019 577167469895466486564029)
                ·
                  refine ⟨216437801210799932461511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577167469895466486564029 216437801210799932461511)
                  ·
                    rfl

theorem cell20_474200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_474200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474200 prefixEnd_474200 := by exact prefixLift 474200
  have htrace : WordTrace (prefixWord ++ tailWord_474200) baseStart_474200 baseEnd_474200 := by
    simpa [prefixWord, tailWord_474200, baseEnd_474200] using wordTrace_append hprefix tailTrace_474200
  have hstable : (prefixWord ++ tailWord_474200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474200).length < 2 ^ (prefixWord ++ tailWord_474200).sum := by decide
  have hdescent : baseEnd_474200 < baseStart_474200 := by decide
  rcases family_descends (prefixWord ++ tailWord_474200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474210 : List Nat := [3, 3, 2, 2, 1, 3, 2, 4]
def baseStart_474210 : Nat := 118140960795 + 474210 * 2 ^ 59
def prefixEnd_474210 : Nat := 4983230072969 + 3 ^ 40 * 474210 * 2
def baseEnd_474210 : Nat := 72147455161094780709379

theorem tailTrace_474210 : CollatzResearch.WordTrace tailWord_474210 prefixEnd_474210 72147455161094780709379 := by
  unfold tailWord_474210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323964903006408366319021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11530573074683755643517389 4323964903006408366319021)
  ·
    refine ⟨1621486838627403137369633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4323964903006408366319021 1621486838627403137369633)
    ·
      refine ⟨1216115128970552353027225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1621486838627403137369633 1216115128970552353027225)
      ·
        refine ⟨912086346727914264770419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216115128970552353027225 912086346727914264770419)
        ·
          refine ⟨1368129520091871397155629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912086346727914264770419 1368129520091871397155629)
          ·
            refine ⟨513048570034451773933361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368129520091871397155629 513048570034451773933361)
            ·
              refine ⟨384786427525838830450021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513048570034451773933361 384786427525838830450021)
              ·
                refine ⟨72147455161094780709379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384786427525838830450021 72147455161094780709379)
                ·
                  rfl

theorem cell20_474210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_474210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474210 prefixEnd_474210 := by exact prefixLift 474210
  have htrace : WordTrace (prefixWord ++ tailWord_474210) baseStart_474210 baseEnd_474210 := by
    simpa [prefixWord, tailWord_474210, baseEnd_474210] using wordTrace_append hprefix tailTrace_474210
  have hstable : (prefixWord ++ tailWord_474210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474210).length < 2 ^ (prefixWord ++ tailWord_474210).sum := by decide
  have hdescent : baseEnd_474210 < baseStart_474210 := by decide
  rcases family_descends (prefixWord ++ tailWord_474210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474221 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_474221 : Nat := 118140960795 + 474221 * 2 ^ 59
def prefixEnd_474221 : Nat := 4983230072969 + 3 ^ 40 * 474221 * 2
def baseEnd_474221 : Nat := 216447386183017192761425

theorem tailTrace_474221 : CollatzResearch.WordTrace tailWord_474221 prefixEnd_474221 216447386183017192761425 := by
  unfold tailWord_474221
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296260814985782343926517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11530840543323854895951011 17296260814985782343926517)
  ·
    refine ⟨1621524451404917094743111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17296260814985782343926517 1621524451404917094743111)
    ·
      refine ⟨2432286677107375642114667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621524451404917094743111 2432286677107375642114667)
      ·
        refine ⟨3648430015661063463172001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432286677107375642114667 3648430015661063463172001)
        ·
          refine ⟨2736322511745797597379001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3648430015661063463172001 2736322511745797597379001)
          ·
            refine ⟨2052241883809348198034251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736322511745797597379001 2052241883809348198034251)
            ·
              refine ⟨3078362825714022297051377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052241883809348198034251 3078362825714022297051377)
              ·
                refine ⟨2308772119285516722788533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078362825714022297051377 2308772119285516722788533)
                ·
                  refine ⟨216447386183017192761425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2308772119285516722788533 216447386183017192761425)
                  ·
                    rfl

theorem cell20_474221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_474221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474221 prefixEnd_474221 := by exact prefixLift 474221
  have htrace : WordTrace (prefixWord ++ tailWord_474221) baseStart_474221 baseEnd_474221 := by
    simpa [prefixWord, tailWord_474221, baseEnd_474221] using wordTrace_append hprefix tailTrace_474221
  have hstable : (prefixWord ++ tailWord_474221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474221).length < 2 ^ (prefixWord ++ tailWord_474221).sum := by decide
  have hdescent : baseEnd_474221 < baseStart_474221 := by decide
  rcases family_descends (prefixWord ++ tailWord_474221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474241 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 2]
def baseStart_474241 : Nat := 118140960795 + 474241 * 2 ^ 59
def prefixEnd_474241 : Nat := 4983230072969 + 3 ^ 40 * 474241 * 2
def baseEnd_474241 : Nat := 216456514727986012094677

theorem tailTrace_474241 : CollatzResearch.WordTrace tailWord_474241 prefixEnd_474241 216456514727986012094677 := by
  unfold tailWord_474241
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296990274913325759654577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11531326849942217173103051 17296990274913325759654577)
  ·
    refine ⟨12972742706184994319740933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17296990274913325759654577 12972742706184994319740933)
    ·
      refine ⟨2432389257409686434951425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12972742706184994319740933 2432389257409686434951425)
      ·
        refine ⟨1824291943057264826213569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432389257409686434951425 1824291943057264826213569)
        ·
          refine ⟨1368218957292948619660177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824291943057264826213569 1368218957292948619660177)
          ·
            refine ⟨1026164217969711464745133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1368218957292948619660177 1026164217969711464745133)
            ·
              refine ⟨384811581738641799279425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026164217969711464745133 384811581738641799279425)
              ·
                refine ⟨288608686303981349459569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384811581738641799279425 288608686303981349459569)
                ·
                  refine ⟨216456514727986012094677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288608686303981349459569 216456514727986012094677)
                  ·
                    rfl

theorem cell20_474241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_474241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474241 prefixEnd_474241 := by exact prefixLift 474241
  have htrace : WordTrace (prefixWord ++ tailWord_474241) baseStart_474241 baseEnd_474241 := by
    simpa [prefixWord, tailWord_474241, baseEnd_474241] using wordTrace_append hprefix tailTrace_474241
  have hstable : (prefixWord ++ tailWord_474241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474241).length < 2 ^ (prefixWord ++ tailWord_474241).sum := by decide
  have hdescent : baseEnd_474241 < baseStart_474241 := by decide
  rcases family_descends (prefixWord ++ tailWord_474241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474273 : List Nat := [1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_474273 : Nat := 118140960795 + 474273 * 2 ^ 59
def prefixEnd_474273 : Nat := 4983230072969 + 3 ^ 40 * 474273 * 2
def baseEnd_474273 : Nat := 72157040133312041009293

theorem tailTrace_474273 : CollatzResearch.WordTrace tailWord_474273 prefixEnd_474273 72157040133312041009293 := by
  unfold tailWord_474273
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298157410797395224819473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11532104940531596816546315 17298157410797395224819473)
  ·
    refine ⟨12973618058098046418614605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17298157410797395224819473 12973618058098046418614605)
    ·
      refine ⟨4865106771786767406980477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12973618058098046418614605 4865106771786767406980477)
      ·
        refine ⟨1824415039420037777617679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4865106771786767406980477 1824415039420037777617679)
        ·
          refine ⟨2736622559130056666426519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824415039420037777617679 2736622559130056666426519)
          ·
            refine ⟨4104933838695084999639779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736622559130056666426519 4104933838695084999639779)
            ·
              refine ⟨6157400758042627499459669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104933838695084999639779 6157400758042627499459669)
              ·
                refine ⟨72157040133312041009293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6157400758042627499459669 72157040133312041009293)
                ·
                  rfl

theorem cell20_474273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_474273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474273 prefixEnd_474273 := by exact prefixLift 474273
  have htrace : WordTrace (prefixWord ++ tailWord_474273) baseStart_474273 baseEnd_474273 := by
    simpa [prefixWord, tailWord_474273, baseEnd_474273] using wordTrace_append hprefix tailTrace_474273
  have hstable : (prefixWord ++ tailWord_474273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474273).length < 2 ^ (prefixWord ++ tailWord_474273).sum := by decide
  have hdescent : baseEnd_474273 < baseStart_474273 := by decide
  rcases family_descends (prefixWord ++ tailWord_474273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474297 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_474297 : Nat := 118140960795 + 474297 * 2 ^ 59
def prefixEnd_474297 : Nat := 4983230072969 + 3 ^ 40 * 474297 * 2
def baseEnd_474297 : Nat := 216482074653898706227781

theorem tailTrace_474297 : CollatzResearch.WordTrace tailWord_474297 prefixEnd_474297 216482074653898706227781 := by
  unfold tailWord_474297
  simp only [CollatzResearch.WordTrace]
  refine ⟨17299032762710447323693145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11532688508473631549128763 17299032762710447323693145)
  ·
    refine ⟨12974274572032835492769859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17299032762710447323693145 12974274572032835492769859)
    ·
      refine ⟨19461411858049253239154789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12974274572032835492769859 19461411858049253239154789)
      ·
        refine ⟨3649014723384234982341523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19461411858049253239154789 3649014723384234982341523)
        ·
          refine ⟨5473522085076352473512285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649014723384234982341523 5473522085076352473512285)
          ·
            refine ⟨2052570781903632177567107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5473522085076352473512285 2052570781903632177567107)
            ·
              refine ⟨3078856172855448266350661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052570781903632177567107 3078856172855448266350661)
              ·
                refine ⟨577285532410396549940749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3078856172855448266350661 577285532410396549940749)
                ·
                  refine ⟨216482074653898706227781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577285532410396549940749 216482074653898706227781)
                  ·
                    rfl

theorem cell20_474297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_474297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474297 prefixEnd_474297 := by exact prefixLift 474297
  have htrace : WordTrace (prefixWord ++ tailWord_474297) baseStart_474297 baseEnd_474297 := by
    simpa [prefixWord, tailWord_474297, baseEnd_474297] using wordTrace_append hprefix tailTrace_474297
  have hstable : (prefixWord ++ tailWord_474297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474297).length < 2 ^ (prefixWord ++ tailWord_474297).sum := by decide
  have hdescent : baseEnd_474297 < baseStart_474297 := by decide
  rcases family_descends (prefixWord ++ tailWord_474297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474300 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 2]
def baseStart_474300 : Nat := 118140960795 + 474300 * 2 ^ 59
def prefixEnd_474300 : Nat := 4983230072969 + 3 ^ 40 * 474300 * 2
def baseEnd_474300 : Nat := 216483443935644029127769

theorem tailTrace_474300 : CollatzResearch.WordTrace tailWord_474300 prefixEnd_474300 216483443935644029127769 := by
  unfold tailWord_474300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649571090849789418026177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11532761454466385890701569 8649571090849789418026177)
  ·
    refine ⟨6487178318137342063519633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8649571090849789418026177 6487178318137342063519633)
    ·
      refine ⟨4865383738603006547639725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487178318137342063519633 4865383738603006547639725)
      ·
        refine ⟨1824518901976127455364897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4865383738603006547639725 1824518901976127455364897)
        ·
          refine ⟨1368389176482095591523673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824518901976127455364897 1368389176482095591523673)
          ·
            refine ⟨1026291882361571693642755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1368389176482095591523673 1026291882361571693642755)
            ·
              refine ⟨1539437823542357540464133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026291882361571693642755 1539437823542357540464133)
              ·
                refine ⟨288644591914192038837025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1539437823542357540464133 288644591914192038837025)
                ·
                  refine ⟨216483443935644029127769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288644591914192038837025 216483443935644029127769)
                  ·
                    rfl

theorem cell20_474300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_474300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474300 prefixEnd_474300 := by exact prefixLift 474300
  have htrace : WordTrace (prefixWord ++ tailWord_474300) baseStart_474300 baseEnd_474300 := by
    simpa [prefixWord, tailWord_474300, baseEnd_474300] using wordTrace_append hprefix tailTrace_474300
  have hstable : (prefixWord ++ tailWord_474300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474300).length < 2 ^ (prefixWord ++ tailWord_474300).sum := by decide
  have hdescent : baseEnd_474300 < baseStart_474300 := by decide
  rcases family_descends (prefixWord ++ tailWord_474300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474317 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 4]
def baseStart_474317 : Nat := 118140960795 + 474317 * 2 ^ 59
def prefixEnd_474317 : Nat := 4983230072969 + 3 ^ 40 * 474317 * 2
def baseEnd_474317 : Nat := 216491203198867525561033

theorem tailTrace_474317 : CollatzResearch.WordTrace tailWord_474317 prefixEnd_474317 216491203198867525561033 := by
  unfold tailWord_474317
  simp only [CollatzResearch.WordTrace]
  refine ⟨17299762222637990739421205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11533174815091993826280803 17299762222637990739421205)
  ·
    refine ⟨810926354186155815910369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17299762222637990739421205 810926354186155815910369)
    ·
      refine ⟨608194765639616861932777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 810926354186155815910369 608194765639616861932777)
      ·
        refine ⟨456146074229712646449583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608194765639616861932777 456146074229712646449583)
        ·
          refine ⟨684219111344568969674375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456146074229712646449583 684219111344568969674375)
          ·
            refine ⟨1026328667016853454511563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684219111344568969674375 1026328667016853454511563)
            ·
              refine ⟨1539493000525280181767345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026328667016853454511563 1539493000525280181767345)
              ·
                refine ⟨1154619750393960136325509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539493000525280181767345 1154619750393960136325509)
                ·
                  refine ⟨216491203198867525561033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154619750393960136325509 216491203198867525561033)
                  ·
                    rfl

theorem cell20_474317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_474317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474317 prefixEnd_474317 := by exact prefixLift 474317
  have htrace : WordTrace (prefixWord ++ tailWord_474317) baseStart_474317 baseEnd_474317 := by
    simpa [prefixWord, tailWord_474317, baseEnd_474317] using wordTrace_append hprefix tailTrace_474317
  have hstable : (prefixWord ++ tailWord_474317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474317).length < 2 ^ (prefixWord ++ tailWord_474317).sum := by decide
  have hdescent : baseEnd_474317 < baseStart_474317 := by decide
  rcases family_descends (prefixWord ++ tailWord_474317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474324 : List Nat := [2, 4, 1, 4, 1, 1, 3, 4]
def baseStart_474324 : Nat := 118140960795 + 474324 * 2 ^ 59
def prefixEnd_474324 : Nat := 4983230072969 + 3 ^ 40 * 474324 * 2
def baseEnd_474324 : Nat := 72164799396535537442557

theorem tailTrace_474324 : CollatzResearch.WordTrace tailWord_474324 prefixEnd_474324 72164799396535537442557 := by
  unfold tailWord_474324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650008766806315467463013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11533345022408420623284017 8650008766806315467463013)
  ·
    refine ⟨1621876643776184150149315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8650008766806315467463013 1621876643776184150149315)
    ·
      refine ⟨2432814965664276225223973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621876643776184150149315 2432814965664276225223973)
      ·
        refine ⟨456152806062051792229495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2432814965664276225223973 456152806062051792229495)
        ·
          refine ⟨684229209093077688344243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456152806062051792229495 684229209093077688344243)
          ·
            refine ⟨1026343813639616532516365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684229209093077688344243 1026343813639616532516365)
            ·
              refine ⟨384878930114856199693637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026343813639616532516365 384878930114856199693637)
              ·
                refine ⟨72164799396535537442557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384878930114856199693637 72164799396535537442557)
                ·
                  rfl

theorem cell20_474324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_474324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474324 prefixEnd_474324 := by exact prefixLift 474324
  have htrace : WordTrace (prefixWord ++ tailWord_474324) baseStart_474324 baseEnd_474324 := by
    simpa [prefixWord, tailWord_474324, baseEnd_474324] using wordTrace_append hprefix tailTrace_474324
  have hstable : (prefixWord ++ tailWord_474324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474324).length < 2 ^ (prefixWord ++ tailWord_474324).sum := by decide
  have hdescent : baseEnd_474324 < baseStart_474324 := by decide
  rcases family_descends (prefixWord ++ tailWord_474324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474380 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_474380 : Nat := 118140960795 + 474380 * 2 ^ 59
def prefixEnd_474380 : Nat := 4983230072969 + 3 ^ 40 * 474380 * 2
def baseEnd_474380 : Nat := 216519958115519306460775

theorem tailTrace_474380 : CollatzResearch.WordTrace tailWord_474380 prefixEnd_474380 216519958115519306460775 := by
  unfold tailWord_474380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651030010704876249482297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11534706680939834999309729 8651030010704876249482297)
  ·
    refine ⟨6488272508028657187111723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8651030010704876249482297 6488272508028657187111723)
    ·
      refine ⟨9732408762042985780667585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488272508028657187111723 9732408762042985780667585)
      ·
        refine ⟨7299306571532239335500689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9732408762042985780667585 7299306571532239335500689)
        ·
          refine ⟨5474479928649179501625517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299306571532239335500689 5474479928649179501625517)
          ·
            refine ⟨2052929973243442313109569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5474479928649179501625517 2052929973243442313109569)
            ·
              refine ⟨1539697479932581734832177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052929973243442313109569 1539697479932581734832177)
              ·
                refine ⟨1154773109949436301124133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539697479932581734832177 1154773109949436301124133)
                ·
                  refine ⟨216519958115519306460775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154773109949436301124133 216519958115519306460775)
                  ·
                    rfl

theorem cell20_474380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_474380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474380 prefixEnd_474380 := by exact prefixLift 474380
  have htrace : WordTrace (prefixWord ++ tailWord_474380) baseStart_474380 baseEnd_474380 := by
    simpa [prefixWord, tailWord_474380, baseEnd_474380] using wordTrace_append hprefix tailTrace_474380
  have hstable : (prefixWord ++ tailWord_474380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474380).length < 2 ^ (prefixWord ++ tailWord_474380).sum := by decide
  have hdescent : baseEnd_474380 < baseStart_474380 := by decide
  rcases family_descends (prefixWord ++ tailWord_474380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474428 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_474428 : Nat := 118140960795 + 474428 * 2 ^ 59
def prefixEnd_474428 : Nat := 4983230072969 + 3 ^ 40 * 474428 * 2
def baseEnd_474428 : Nat := 216541866623444472860579

theorem tailTrace_474428 : CollatzResearch.WordTrace tailWord_474428 prefixEnd_474428 216541866623444472860579 := by
  unfold tailWord_474428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651905362617928348355969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11535873816823904464474625 8651905362617928348355969)
  ·
    refine ⟨6488929021963446261266977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8651905362617928348355969 6488929021963446261266977)
    ·
      refine ⟨4866696766472584695950233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6488929021963446261266977 4866696766472584695950233)
      ·
        refine ⟨3650022574854438521962675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4866696766472584695950233 3650022574854438521962675)
        ·
          refine ⟨5475033862281657782944013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650022574854438521962675 5475033862281657782944013)
          ·
            refine ⟨2053137698355621668604005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5475033862281657782944013 2053137698355621668604005)
            ·
              refine ⟨384963318441679062863251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2053137698355621668604005 384963318441679062863251)
              ·
                refine ⟨577444977662518594294877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384963318441679062863251 577444977662518594294877)
                ·
                  refine ⟨216541866623444472860579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577444977662518594294877 216541866623444472860579)
                  ·
                    rfl

theorem cell20_474428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_474428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474428 prefixEnd_474428 := by exact prefixLift 474428
  have htrace : WordTrace (prefixWord ++ tailWord_474428) baseStart_474428 baseEnd_474428 := by
    simpa [prefixWord, tailWord_474428, baseEnd_474428] using wordTrace_append hprefix tailTrace_474428
  have hstable : (prefixWord ++ tailWord_474428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474428).length < 2 ^ (prefixWord ++ tailWord_474428).sum := by decide
  have hdescent : baseEnd_474428 < baseStart_474428 := by decide
  rcases family_descends (prefixWord ++ tailWord_474428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474466 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_474466 : Nat := 118140960795 + 474466 * 2 ^ 59
def prefixEnd_474466 : Nat := 4983230072969 + 3 ^ 40 * 474466 * 2
def baseEnd_474466 : Nat := 216559210858885229593757

theorem tailTrace_474466 : CollatzResearch.WordTrace tailWord_474466 prefixEnd_474466 216559210858885229593757 := by
  unfold tailWord_474466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326299174774547296648813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11536797799398792791063501 4326299174774547296648813)
  ·
    refine ⟨1622362190540455236243305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4326299174774547296648813 1622362190540455236243305)
    ·
      refine ⟨1216771642905341427182479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1622362190540455236243305 1216771642905341427182479)
      ·
        refine ⟨1825157464358012140773719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216771642905341427182479 1825157464358012140773719)
        ·
          refine ⟨2737736196537018211160579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825157464358012140773719 2737736196537018211160579)
          ·
            refine ⟨4106604294805527316740869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737736196537018211160579 4106604294805527316740869)
            ·
              refine ⟨769988305276036371888913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4106604294805527316740869 769988305276036371888913)
              ·
                refine ⟨577491228957027278916685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769988305276036371888913 577491228957027278916685)
                ·
                  refine ⟨216559210858885229593757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577491228957027278916685 216559210858885229593757)
                  ·
                    rfl

theorem cell20_474466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_474466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474466 prefixEnd_474466 := by exact prefixLift 474466
  have htrace : WordTrace (prefixWord ++ tailWord_474466) baseStart_474466 baseEnd_474466 := by
    simpa [prefixWord, tailWord_474466, baseEnd_474466] using wordTrace_append hprefix tailTrace_474466
  have hstable : (prefixWord ++ tailWord_474466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474466).length < 2 ^ (prefixWord ++ tailWord_474466).sum := by decide
  have hdescent : baseEnd_474466 < baseStart_474466 := by decide
  rcases family_descends (prefixWord ++ tailWord_474466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474497 : List Nat := [1, 2, 4, 3, 2, 1, 3, 4]
def baseStart_474497 : Nat := 118140960795 + 474497 * 2 ^ 59
def prefixEnd_474497 : Nat := 4983230072969 + 3 ^ 40 * 474497 * 2
def baseEnd_474497 : Nat := 72191120034528966520099

theorem tailTrace_474497 : CollatzResearch.WordTrace tailWord_474497 prefixEnd_474497 72191120034528966520099 := by
  unfold tailWord_474497
  simp only [CollatzResearch.WordTrace]
  refine ⟨17306327361985881480973745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11537551574657254320649163 17306327361985881480973745)
  ·
    refine ⟨12979745521489411110730309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17306327361985881480973745 12979745521489411110730309)
    ·
      refine ⟨2433702285279264583261933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12979745521489411110730309 2433702285279264583261933)
      ·
        refine ⟨912638356979724218723225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2433702285279264583261933 912638356979724218723225)
        ·
          refine ⟨684478767734793164042419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912638356979724218723225 684478767734793164042419)
          ·
            refine ⟨1026718151602189746063629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684478767734793164042419 1026718151602189746063629)
            ·
              refine ⟨385019306850821154773861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026718151602189746063629 385019306850821154773861)
              ·
                refine ⟨72191120034528966520099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385019306850821154773861 72191120034528966520099)
                ·
                  rfl

theorem cell20_474497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_474497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474497 prefixEnd_474497 := by exact prefixLift 474497
  have htrace : WordTrace (prefixWord ++ tailWord_474497) baseStart_474497 baseEnd_474497 := by
    simpa [prefixWord, tailWord_474497, baseEnd_474497] using wordTrace_append hprefix tailTrace_474497
  have hstable : (prefixWord ++ tailWord_474497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474497).length < 2 ^ (prefixWord ++ tailWord_474497).sum := by decide
  have hdescent : baseEnd_474497 < baseStart_474497 := by decide
  rcases family_descends (prefixWord ++ tailWord_474497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474508 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_474508 : Nat := 118140960795 + 474508 * 2 ^ 59
def prefixEnd_474508 : Nat := 4983230072969 + 3 ^ 40 * 474508 * 2
def baseEnd_474508 : Nat := 216578380803319750193585

theorem tailTrace_474508 : CollatzResearch.WordTrace tailWord_474508 prefixEnd_474508 216578380803319750193585 := by
  unfold tailWord_474508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653364282473015179812089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11537819043297353573082785 8653364282473015179812089)
  ·
    refine ⟨6490023211854761384859067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8653364282473015179812089 6490023211854761384859067)
    ·
      refine ⟨9735034817782142077288601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490023211854761384859067 9735034817782142077288601)
      ·
        refine ⟨7301276113336606557966451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9735034817782142077288601 7301276113336606557966451)
        ·
          refine ⟨10951914170004909836949677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301276113336606557966451 10951914170004909836949677)
          ·
            refine ⟨4106967813751841188856129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10951914170004909836949677 4106967813751841188856129)
            ·
              refine ⟨3080225860313880891642097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106967813751841188856129 3080225860313880891642097)
              ·
                refine ⟨2310169395235410668731573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3080225860313880891642097 2310169395235410668731573)
                ·
                  refine ⟨216578380803319750193585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310169395235410668731573 216578380803319750193585)
                  ·
                    rfl

theorem cell20_474508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_474508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474508 prefixEnd_474508 := by exact prefixLift 474508
  have htrace : WordTrace (prefixWord ++ tailWord_474508) baseStart_474508 baseEnd_474508 := by
    simpa [prefixWord, tailWord_474508, baseEnd_474508] using wordTrace_append hprefix tailTrace_474508
  have hstable : (prefixWord ++ tailWord_474508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474508).length < 2 ^ (prefixWord ++ tailWord_474508).sum := by decide
  have hdescent : baseEnd_474508 < baseStart_474508 := by decide
  rcases family_descends (prefixWord ++ tailWord_474508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474525 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_474525 : Nat := 118140960795 + 474525 * 2 ^ 59
def prefixEnd_474525 : Nat := 4983230072969 + 3 ^ 40 * 474525 * 2
def baseEnd_474525 : Nat := 216586140066543246626849

theorem tailTrace_474525 : CollatzResearch.WordTrace tailWord_474525 prefixEnd_474525 216586140066543246626849 := by
  unfold tailWord_474525
  simp only [CollatzResearch.WordTrace]
  refine ⟨17307348605884442262993029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11538232403922961508662019 17307348605884442262993029)
  ·
    refine ⟨3245127863603332924311193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17307348605884442262993029 3245127863603332924311193)
    ·
      refine ⟨2433845897702499693233395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3245127863603332924311193 2433845897702499693233395)
      ·
        refine ⟨3650768846553749539850093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433845897702499693233395 3650768846553749539850093)
        ·
          refine ⟨1369038317457656077443785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3650768846553749539850093 1369038317457656077443785)
          ·
            refine ⟨1026778738093242058082839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369038317457656077443785 1026778738093242058082839)
            ·
              refine ⟨1540168107139863087124259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026778738093242058082839 1540168107139863087124259)
              ·
                refine ⟨2310252160709794630686389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540168107139863087124259 2310252160709794630686389)
                ·
                  refine ⟨216586140066543246626849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310252160709794630686389 216586140066543246626849)
                  ·
                    rfl

theorem cell20_474525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_474525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474525 prefixEnd_474525 := by exact prefixLift 474525
  have htrace : WordTrace (prefixWord ++ tailWord_474525) baseStart_474525 baseEnd_474525 := by
    simpa [prefixWord, tailWord_474525, baseEnd_474525] using wordTrace_append hprefix tailTrace_474525
  have hstable : (prefixWord ++ tailWord_474525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474525).length < 2 ^ (prefixWord ++ tailWord_474525).sum := by decide
  have hdescent : baseEnd_474525 < baseStart_474525 := by decide
  rcases family_descends (prefixWord ++ tailWord_474525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474556 : List Nat := [2, 2, 2, 4, 2, 1, 1, 6]
def baseStart_474556 : Nat := 118140960795 + 474556 * 2 ^ 59
def prefixEnd_474556 : Nat := 4983230072969 + 3 ^ 40 * 474556 * 2
def baseEnd_474556 : Nat := 72200096437081638864463

theorem tailTrace_474556 : CollatzResearch.WordTrace tailWord_474556 prefixEnd_474556 72200096437081638864463 := by
  unfold tailWord_474556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654239634386067278685761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11538986179181423038247681 8654239634386067278685761)
  ·
    refine ⟨6490679725789550459014321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8654239634386067278685761 6490679725789550459014321)
    ·
      refine ⟨4868009794342162844260741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6490679725789550459014321 4868009794342162844260741)
      ·
        refine ⟨912751836439155533298889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4868009794342162844260741 912751836439155533298889)
        ·
          refine ⟨684563877329366649974167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 912751836439155533298889 684563877329366649974167)
          ·
            refine ⟨1026845815994049974961251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684563877329366649974167 1026845815994049974961251)
            ·
              refine ⟨1540268723991074962441877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026845815994049974961251 1540268723991074962441877)
              ·
                refine ⟨72200096437081638864463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1540268723991074962441877 72200096437081638864463)
                ·
                  rfl

theorem cell20_474556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_474556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474556 prefixEnd_474556 := by exact prefixLift 474556
  have htrace : WordTrace (prefixWord ++ tailWord_474556) baseStart_474556 baseEnd_474556 := by
    simpa [prefixWord, tailWord_474556, baseEnd_474556] using wordTrace_append hprefix tailTrace_474556
  have hstable : (prefixWord ++ tailWord_474556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474556).length < 2 ^ (prefixWord ++ tailWord_474556).sum := by decide
  have hdescent : baseEnd_474556 < baseStart_474556 := by decide
  rcases family_descends (prefixWord ++ tailWord_474556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474584 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_474584 : Nat := 118140960795 + 474584 * 2 ^ 59
def prefixEnd_474584 : Nat := 4983230072969 + 3 ^ 40 * 474584 * 2
def baseEnd_474584 : Nat := 216613069274201263659941

theorem tailTrace_474584 : CollatzResearch.WordTrace tailWord_474584 prefixEnd_474584 216613069274201263659941 := by
  unfold tailWord_474584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654750256335347669695403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11539667008447130226260537 8654750256335347669695403)
  ·
    refine ⟨12982125384503021504543105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654750256335347669695403 12982125384503021504543105)
    ·
      refine ⟨9736594038377266128407329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12982125384503021504543105 9736594038377266128407329)
      ·
        refine ⟨7302445528782949596305497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9736594038377266128407329 7302445528782949596305497)
        ·
          refine ⟨5476834146587212197229123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7302445528782949596305497 5476834146587212197229123)
          ·
            refine ⟨8215251219880818295843685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476834146587212197229123 8215251219880818295843685)
            ·
              refine ⟨1540359603727653430470691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8215251219880818295843685 1540359603727653430470691)
              ·
                refine ⟨2310539405591480145706037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540359603727653430470691 2310539405591480145706037)
                ·
                  refine ⟨216613069274201263659941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2310539405591480145706037 216613069274201263659941)
                  ·
                    rfl

theorem cell20_474584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_474584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474584 prefixEnd_474584 := by exact prefixLift 474584
  have htrace : WordTrace (prefixWord ++ tailWord_474584) baseStart_474584 baseEnd_474584 := by
    simpa [prefixWord, tailWord_474584, baseEnd_474584] using wordTrace_append hprefix tailTrace_474584
  have hstable : (prefixWord ++ tailWord_474584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474584).length < 2 ^ (prefixWord ++ tailWord_474584).sum := by decide
  have hdescent : baseEnd_474584 < baseStart_474584 := by decide
  rcases family_descends (prefixWord ++ tailWord_474584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474597 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 3]
def baseStart_474597 : Nat := 118140960795 + 474597 * 2 ^ 59
def prefixEnd_474597 : Nat := 4983230072969 + 3 ^ 40 * 474597 * 2
def baseEnd_474597 : Nat := 216619002828430996226555

theorem tailTrace_474597 : CollatzResearch.WordTrace tailWord_474597 prefixEnd_474597 216619002828430996226555 := by
  unfold tailWord_474597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309974661623598559614045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11539983107749065706409363 17309974661623598559614045)
  ·
    refine ⟨6491240498108849459855267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17309974661623598559614045 6491240498108849459855267)
    ·
      refine ⟨9736860747163274189782901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6491240498108849459855267 9736860747163274189782901)
      ·
        refine ⟨912830695046556955292147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9736860747163274189782901 912830695046556955292147)
        ·
          refine ⟨1369246042569835432938221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912830695046556955292147 1369246042569835432938221)
          ·
            refine ⟨513467265963688287351833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1369246042569835432938221 513467265963688287351833)
            ·
              refine ⟨385100449472766215513875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513467265963688287351833 385100449472766215513875)
              ·
                refine ⟨577650674209149323270813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385100449472766215513875 577650674209149323270813)
                ·
                  refine ⟨216619002828430996226555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577650674209149323270813 216619002828430996226555)
                  ·
                    rfl

theorem cell20_474597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_474597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474597 prefixEnd_474597 := by exact prefixLift 474597
  have htrace : WordTrace (prefixWord ++ tailWord_474597) baseStart_474597 baseEnd_474597 := by
    simpa [prefixWord, tailWord_474597, baseEnd_474597] using wordTrace_append hprefix tailTrace_474597
  have hstable : (prefixWord ++ tailWord_474597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474597).length < 2 ^ (prefixWord ++ tailWord_474597).sum := by decide
  have hdescent : baseEnd_474597 < baseStart_474597 := by decide
  rcases family_descends (prefixWord ++ tailWord_474597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474636 : List Nat := [2, 2, 1, 2, 13]
def baseStart_474636 : Nat := 118140960795 + 474636 * 2 ^ 59
def prefixEnd_474636 : Nat := 4983230072969 + 3 ^ 40 * 474636 * 2
def baseEnd_474636 : Nat := 2674528438161977702795

theorem tailTrace_474636 : CollatzResearch.WordTrace tailWord_474636 prefixEnd_474636 2674528438161977702795 := by
  unfold tailWord_474636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655698554241154110141881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11540931405654872146855841 8655698554241154110141881)
  ·
    refine ⟨6491773915680865582606411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8655698554241154110141881 6491773915680865582606411)
    ·
      refine ⟨9737660873521298373909617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6491773915680865582606411 9737660873521298373909617)
      ·
        refine ⟨7303245655140973780432213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9737660873521298373909617 7303245655140973780432213)
        ·
          refine ⟨2674528438161977702795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7303245655140973780432213 2674528438161977702795)
          ·
            rfl

theorem cell20_474636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 13].length) (baseStart_474636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474636 prefixEnd_474636 := by exact prefixLift 474636
  have htrace : WordTrace (prefixWord ++ tailWord_474636) baseStart_474636 baseEnd_474636 := by
    simpa [prefixWord, tailWord_474636, baseEnd_474636] using wordTrace_append hprefix tailTrace_474636
  have hstable : (prefixWord ++ tailWord_474636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474636).length < 2 ^ (prefixWord ++ tailWord_474636).sum := by decide
  have hdescent : baseEnd_474636 < baseStart_474636 := by decide
  rcases family_descends (prefixWord ++ tailWord_474636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474638 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_474638 : Nat := 118140960795 + 474638 * 2 ^ 59
def prefixEnd_474638 : Nat := 4983230072969 + 3 ^ 40 * 474638 * 2
def baseEnd_474638 : Nat := 216637716345617075859721

theorem tailTrace_474638 : CollatzResearch.WordTrace tailWord_474638 prefixEnd_474638 216637716345617075859721 := by
  unfold tailWord_474638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163933756809382820232071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11540980036316708374571045 2163933756809382820232071)
  ·
    refine ⟨3245900635214074230348107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2163933756809382820232071 3245900635214074230348107)
    ·
      refine ⟨4868850952821111345522161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245900635214074230348107 4868850952821111345522161)
      ·
        refine ⟨3651638214615833509141621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4868850952821111345522161 3651638214615833509141621)
        ·
          refine ⟨342341082620234391482027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3651638214615833509141621 342341082620234391482027)
          ·
            refine ⟨513511623930351587223041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342341082620234391482027 513511623930351587223041)
            ·
              refine ⟨385133717947763690417281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513511623930351587223041 385133717947763690417281)
              ·
                refine ⟨288850288460822767812961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385133717947763690417281 288850288460822767812961)
                ·
                  refine ⟨216637716345617075859721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288850288460822767812961 216637716345617075859721)
                  ·
                    rfl

theorem cell20_474638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_474638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474638 prefixEnd_474638 := by exact prefixLift 474638
  have htrace : WordTrace (prefixWord ++ tailWord_474638) baseStart_474638 baseEnd_474638 := by
    simpa [prefixWord, tailWord_474638, baseEnd_474638] using wordTrace_append hprefix tailTrace_474638
  have hstable : (prefixWord ++ tailWord_474638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474638).length < 2 ^ (prefixWord ++ tailWord_474638).sum := by decide
  have hdescent : baseEnd_474638 < baseStart_474638 := by decide
  rcases family_descends (prefixWord ++ tailWord_474638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474698 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_474698 : Nat := 118140960795 + 474698 * 2 ^ 59
def prefixEnd_474698 : Nat := 4983230072969 + 3 ^ 40 * 474698 * 2
def baseEnd_474698 : Nat := 216665101980523533859475

theorem tailTrace_474698 : CollatzResearch.WordTrace tailWord_474698 prefixEnd_474698 216665101980523533859475 := by
  unfold tailWord_474698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328414608564423202260187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11542438956171795206027165 4328414608564423202260187)
  ·
    refine ⟨6492621912846634803390281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4328414608564423202260187 6492621912846634803390281)
    ·
      refine ⟨4869466434634976102542711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6492621912846634803390281 4869466434634976102542711)
      ·
        refine ⟨7304199651952464153814067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869466434634976102542711 7304199651952464153814067)
        ·
          refine ⟨10956299477928696230721101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304199651952464153814067 10956299477928696230721101)
          ·
            refine ⟨4108612304223261086520413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10956299477928696230721101 4108612304223261086520413)
            ·
              refine ⟨1540729614083722907445155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4108612304223261086520413 1540729614083722907445155)
              ·
                refine ⟨2311094421125584361167733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540729614083722907445155 2311094421125584361167733)
                ·
                  refine ⟨216665101980523533859475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311094421125584361167733 216665101980523533859475)
                  ·
                    rfl

theorem cell20_474698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_474698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474698 prefixEnd_474698 := by exact prefixLift 474698
  have htrace : WordTrace (prefixWord ++ tailWord_474698) baseStart_474698 baseEnd_474698 := by
    simpa [prefixWord, tailWord_474698, baseEnd_474698] using wordTrace_append hprefix tailTrace_474698
  have hstable : (prefixWord ++ tailWord_474698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474698).length < 2 ^ (prefixWord ++ tailWord_474698).sum := by decide
  have hdescent : baseEnd_474698 < baseStart_474698 := by decide
  rcases family_descends (prefixWord ++ tailWord_474698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474712 : List Nat := [2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_474712 : Nat := 118140960795 + 474712 * 2 ^ 59
def prefixEnd_474712 : Nat := 4983230072969 + 3 ^ 40 * 474712 * 2
def baseEnd_474712 : Nat := 72223830654000569130917

theorem tailTrace_474712 : CollatzResearch.WordTrace tailWord_474712 prefixEnd_474712 72223830654000569130917 := by
  unfold tailWord_474712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657084528103486600025195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11542779370804648800033593 8657084528103486600025195)
  ·
    refine ⟨12985626792155229900037793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8657084528103486600025195 12985626792155229900037793)
    ·
      refine ⟨9739220094116422425028345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12985626792155229900037793 9739220094116422425028345)
      ·
        refine ⟨7304415070587316818771259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9739220094116422425028345 7304415070587316818771259)
        ·
          refine ⟨10956622605880975228156889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7304415070587316818771259 10956622605880975228156889)
          ·
            refine ⟨8217466954410731421117667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10956622605880975228156889 8217466954410731421117667)
            ·
              refine ⟨12326200431616097131676501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8217466954410731421117667 12326200431616097131676501)
              ·
                refine ⟨72223830654000569130917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12326200431616097131676501 72223830654000569130917)
                ·
                  rfl

theorem cell20_474712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_474712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474712 prefixEnd_474712 := by exact prefixLift 474712
  have htrace : WordTrace (prefixWord ++ tailWord_474712) baseStart_474712 baseEnd_474712 := by
    simpa [prefixWord, tailWord_474712, baseEnd_474712] using wordTrace_append hprefix tailTrace_474712
  have hstable : (prefixWord ++ tailWord_474712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474712).length < 2 ^ (prefixWord ++ tailWord_474712).sum := by decide
  have hdescent : baseEnd_474712 < baseStart_474712 := by decide
  rcases family_descends (prefixWord ++ tailWord_474712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474729 : List Nat := [1, 2, 1, 1, 1, 4, 6, 4]
def baseStart_474729 : Nat := 118140960795 + 474729 * 2 ^ 59
def prefixEnd_474729 : Nat := 4983230072969 + 3 ^ 40 * 474729 * 2
def baseEnd_474729 : Nat := 72226417075075067942005

theorem tailTrace_474729 : CollatzResearch.WordTrace tailWord_474729 prefixEnd_474729 72226417075075067942005 := by
  unfold tailWord_474729
  simp only [CollatzResearch.WordTrace]
  refine ⟨17314789097145385103419241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11543192731430256735612827 17314789097145385103419241)
  ·
    refine ⟨12986091822859038827564431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17314789097145385103419241 12986091822859038827564431)
    ·
      refine ⟨19479137734288558241346647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12986091822859038827564431 19479137734288558241346647)
      ·
        refine ⟨29218706601432837362019971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19479137734288558241346647 29218706601432837362019971)
        ·
          refine ⟨43828059902149256043029957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29218706601432837362019971 43828059902149256043029957)
          ·
            refine ⟨8217761231652985508068117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43828059902149256043029957 8217761231652985508068117)
            ·
              refine ⟨385207557733733695690693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8217761231652985508068117 385207557733733695690693)
              ·
                refine ⟨72226417075075067942005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385207557733733695690693 72226417075075067942005)
                ·
                  rfl

theorem cell20_474729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_474729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474729 prefixEnd_474729 := by exact prefixLift 474729
  have htrace : WordTrace (prefixWord ++ tailWord_474729) baseStart_474729 baseEnd_474729 := by
    simpa [prefixWord, tailWord_474729, baseEnd_474729] using wordTrace_append hprefix tailTrace_474729
  have hstable : (prefixWord ++ tailWord_474729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474729).length < 2 ^ (prefixWord ++ tailWord_474729).sum := by decide
  have hdescent : baseEnd_474729 < baseStart_474729 := by decide
  rcases family_descends (prefixWord ++ tailWord_474729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474736 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_474736 : Nat := 118140960795 + 474736 * 2 ^ 59
def prefixEnd_474736 : Nat := 4983230072969 + 3 ^ 40 * 474736 * 2
def baseEnd_474736 : Nat := 216682446215964290592653

theorem tailTrace_474736 : CollatzResearch.WordTrace tailWord_474736 prefixEnd_474736 216682446215964290592653 := by
  unfold tailWord_474736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657522204060012649462031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11543362938746683532616041 8657522204060012649462031)
  ·
    refine ⟨12986283306090018974193047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8657522204060012649462031 12986283306090018974193047)
    ·
      refine ⟨19479424959135028461289571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12986283306090018974193047 19479424959135028461289571)
      ·
        refine ⟨29219137438702542691934357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19479424959135028461289571 29219137438702542691934357)
        ·
          refine ⟨1369647067439181688684423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29219137438702542691934357 1369647067439181688684423)
          ·
            refine ⟨2054470601158772533026635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369647067439181688684423 2054470601158772533026635)
            ·
              refine ⟨3081705901738158799539953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054470601158772533026635 3081705901738158799539953)
              ·
                refine ⟨2311279426303619099654965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081705901738158799539953 2311279426303619099654965)
                ·
                  refine ⟨216682446215964290592653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2311279426303619099654965 216682446215964290592653)
                  ·
                    rfl

theorem cell20_474736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_474736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474736 prefixEnd_474736 := by exact prefixLift 474736
  have htrace : WordTrace (prefixWord ++ tailWord_474736) baseStart_474736 baseEnd_474736 := by
    simpa [prefixWord, tailWord_474736, baseEnd_474736] using wordTrace_append hprefix tailTrace_474736
  have hstable : (prefixWord ++ tailWord_474736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474736).length < 2 ^ (prefixWord ++ tailWord_474736).sum := by decide
  have hdescent : baseEnd_474736 < baseStart_474736 := by decide
  rcases family_descends (prefixWord ++ tailWord_474736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474756 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 4]
def baseStart_474756 : Nat := 118140960795 + 474756 * 2 ^ 59
def prefixEnd_474756 : Nat := 4983230072969 + 3 ^ 40 * 474756 * 2
def baseEnd_474756 : Nat := 216691574760933109925905

theorem tailTrace_474756 : CollatzResearch.WordTrace tailWord_474756 prefixEnd_474756 216691574760933109925905 := by
  unfold tailWord_474756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8657886934023784357326061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11543849245365045809768081 8657886934023784357326061)
  ·
    refine ⟨3246707600258919133997273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8657886934023784357326061 3246707600258919133997273)
    ·
      refine ⟨2435030700194189350497955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3246707600258919133997273 2435030700194189350497955)
      ·
        refine ⟨3652546050291284025746933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435030700194189350497955 3652546050291284025746933)
        ·
          refine ⟨342426192214807877413775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3652546050291284025746933 342426192214807877413775)
          ·
            refine ⟨513639288322211816120663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342426192214807877413775 513639288322211816120663)
            ·
              refine ⟨770458932483317724180995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513639288322211816120663 770458932483317724180995)
              ·
                refine ⟨1155688398724976586271493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770458932483317724180995 1155688398724976586271493)
                ·
                  refine ⟨216691574760933109925905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1155688398724976586271493 216691574760933109925905)
                  ·
                    rfl

theorem cell20_474756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_474756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474756 prefixEnd_474756 := by exact prefixLift 474756
  have htrace : WordTrace (prefixWord ++ tailWord_474756) baseStart_474756 baseEnd_474756 := by
    simpa [prefixWord, tailWord_474756, baseEnd_474756] using wordTrace_append hprefix tailTrace_474756
  have hstable : (prefixWord ++ tailWord_474756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474756).length < 2 ^ (prefixWord ++ tailWord_474756).sum := by decide
  have hdescent : baseEnd_474756 < baseStart_474756 := by decide
  rcases family_descends (prefixWord ++ tailWord_474756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474770 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_474770 : Nat := 118140960795 + 474770 * 2 ^ 59
def prefixEnd_474770 : Nat := 4983230072969 + 3 ^ 40 * 474770 * 2
def baseEnd_474770 : Nat := 216697964742411283459181

theorem tailTrace_474770 : CollatzResearch.WordTrace tailWord_474770 prefixEnd_474770 216697964742411283459181 := by
  unfold tailWord_474770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329071122499212276415441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11544189659997899403774509 4329071122499212276415441)
  ·
    refine ⟨3246803341874409207311581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4329071122499212276415441 3246803341874409207311581)
    ·
      refine ⟨1217551253202903452741843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3246803341874409207311581 1217551253202903452741843)
      ·
        refine ⟨1826326879804355179112765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217551253202903452741843 1826326879804355179112765)
        ·
          refine ⟨684872579926633192167287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1826326879804355179112765 684872579926633192167287)
          ·
            refine ⟨1027308869889949788250931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684872579926633192167287 1027308869889949788250931)
            ·
              refine ⟨1540963304834924682376397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027308869889949788250931 1540963304834924682376397)
              ·
                refine ⟨577861239313096755891149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1540963304834924682376397 577861239313096755891149)
                ·
                  refine ⟨216697964742411283459181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577861239313096755891149 216697964742411283459181)
                  ·
                    rfl

theorem cell20_474770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_474770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474770 prefixEnd_474770 := by exact prefixLift 474770
  have htrace : WordTrace (prefixWord ++ tailWord_474770) baseStart_474770 baseEnd_474770 := by
    simpa [prefixWord, tailWord_474770, baseEnd_474770] using wordTrace_append hprefix tailTrace_474770
  have hstable : (prefixWord ++ tailWord_474770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474770).length < 2 ^ (prefixWord ++ tailWord_474770).sum := by decide
  have hdescent : baseEnd_474770 < baseStart_474770 := by decide
  rcases family_descends (prefixWord ++ tailWord_474770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474781 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_474781 : Nat := 118140960795 + 474781 * 2 ^ 59
def prefixEnd_474781 : Nat := 4983230072969 + 3 ^ 40 * 474781 * 2
def baseEnd_474781 : Nat := 216702985442144134092469

theorem tailTrace_474781 : CollatzResearch.WordTrace tailWord_474781 prefixEnd_474781 216702985442144134092469 := by
  unfold tailWord_474781
  simp only [CollatzResearch.WordTrace]
  refine ⟨17316685692956997984312197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11544457128637998656208131 17316685692956997984312197)
  ·
    refine ⟨3246878567429437122058537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17316685692956997984312197 3246878567429437122058537)
    ·
      refine ⟨2435158925572077841543903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3246878567429437122058537 2435158925572077841543903)
      ·
        refine ⟨3652738388358116762315855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435158925572077841543903 3652738388358116762315855)
        ·
          refine ⟨5479107582537175143473783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652738388358116762315855 5479107582537175143473783)
          ·
            refine ⟨8218661373805762715210675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479107582537175143473783 8218661373805762715210675)
            ·
              refine ⟨12327992060708644072816013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218661373805762715210675 12327992060708644072816013)
              ·
                refine ⟨4622997022765741527306005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12327992060708644072816013 4622997022765741527306005)
                ·
                  refine ⟨216702985442144134092469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4622997022765741527306005 216702985442144134092469)
                  ·
                    rfl

theorem cell20_474781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_474781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474781 prefixEnd_474781 := by exact prefixLift 474781
  have htrace : WordTrace (prefixWord ++ tailWord_474781) baseStart_474781 baseEnd_474781 := by
    simpa [prefixWord, tailWord_474781, baseEnd_474781] using wordTrace_append hprefix tailTrace_474781
  have hstable : (prefixWord ++ tailWord_474781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474781).length < 2 ^ (prefixWord ++ tailWord_474781).sum := by decide
  have hdescent : baseEnd_474781 < baseStart_474781 := by decide
  rcases family_descends (prefixWord ++ tailWord_474781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474805 : List Nat := [1, 3, 3, 3, 2, 8]
def baseStart_474805 : Nat := 118140960795 + 474805 * 2 ^ 59
def prefixEnd_474805 : Nat := 4983230072969 + 3 ^ 40 * 474805 * 2
def baseEnd_474805 : Nat := 8026442210966915455273

theorem tailTrace_474805 : CollatzResearch.WordTrace tailWord_474805 prefixEnd_474805 8026442210966915455273 := by
  unfold tailWord_474805
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317561044870050083185869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11545040696580033388790579 17317561044870050083185869)
  ·
    refine ⟨6494085391826268781194701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17317561044870050083185869 6494085391826268781194701)
    ·
      refine ⟨2435282021934850792948013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6494085391826268781194701 2435282021934850792948013)
      ·
        refine ⟨913230758225569047355505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2435282021934850792948013 913230758225569047355505)
        ·
          refine ⟨684923068669176785516629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913230758225569047355505 684923068669176785516629)
          ·
            refine ⟨8026442210966915455273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 684923068669176785516629 8026442210966915455273)
            ·
              rfl

theorem cell20_474805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 8].length) (baseStart_474805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474805 prefixEnd_474805 := by exact prefixLift 474805
  have htrace : WordTrace (prefixWord ++ tailWord_474805) baseStart_474805 baseEnd_474805 := by
    simpa [prefixWord, tailWord_474805, baseEnd_474805] using wordTrace_append hprefix tailTrace_474805
  have hstable : (prefixWord ++ tailWord_474805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474805).length < 2 ^ (prefixWord ++ tailWord_474805).sum := by decide
  have hdescent : baseEnd_474805 < baseStart_474805 := by decide
  rcases family_descends (prefixWord ++ tailWord_474805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474836 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_474836 : Nat := 118140960795 + 474836 * 2 ^ 59
def prefixEnd_474836 : Nat := 4983230072969 + 3 ^ 40 * 474836 * 2
def baseEnd_474836 : Nat := 216728088940808387258911

theorem tailTrace_474836 : CollatzResearch.WordTrace tailWord_474836 prefixEnd_474836 216728088940808387258911 := by
  unfold tailWord_474836
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659345853878871188782181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11545794471838494918376241 8659345853878871188782181)
  ·
    refine ⟨1623627347602288347896659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8659345853878871188782181 1623627347602288347896659)
    ·
      refine ⟨2435441021403432521844989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623627347602288347896659 2435441021403432521844989)
      ·
        refine ⟨913290383026287195691871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2435441021403432521844989 913290383026287195691871)
        ·
          refine ⟨1369935574539430793537807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913290383026287195691871 1369935574539430793537807)
          ·
            refine ⟨2054903361809146190306711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369935574539430793537807 2054903361809146190306711)
            ·
              refine ⟨3082355042713719285460067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054903361809146190306711 3082355042713719285460067)
              ·
                refine ⟨4623532564070578928190101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082355042713719285460067 4623532564070578928190101)
                ·
                  refine ⟨216728088940808387258911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4623532564070578928190101 216728088940808387258911)
                  ·
                    rfl

theorem cell20_474836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_474836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474836 prefixEnd_474836 := by exact prefixLift 474836
  have htrace : WordTrace (prefixWord ++ tailWord_474836) baseStart_474836 baseEnd_474836 := by
    simpa [prefixWord, tailWord_474836, baseEnd_474836] using wordTrace_append hprefix tailTrace_474836
  have hstable : (prefixWord ++ tailWord_474836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474836).length < 2 ^ (prefixWord ++ tailWord_474836).sum := by decide
  have hdescent : baseEnd_474836 < baseStart_474836 := by decide
  rcases family_descends (prefixWord ++ tailWord_474836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474853 : List Nat := [1, 3, 1, 4, 1, 1, 4, 3, 2]
def baseStart_474853 : Nat := 118140960795 + 474853 * 2 ^ 59
def prefixEnd_474853 : Nat := 4983230072969 + 3 ^ 40 * 474853 * 2
def baseEnd_474853 : Nat := 216735848204031883692175

theorem tailTrace_474853 : CollatzResearch.WordTrace tailWord_474853 prefixEnd_474853 216735848204031883692175 := by
  unfold tailWord_474853
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319311748696154280933213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11546207832464102853955475 17319311748696154280933213)
  ·
    refine ⟨6494741905761057855349955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17319311748696154280933213 6494741905761057855349955)
    ·
      refine ⟨9742112858641586783024933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494741905761057855349955 9742112858641586783024933)
      ·
        refine ⟨1826646160995297521817175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9742112858641586783024933 1826646160995297521817175)
        ·
          refine ⟨2739969241492946282725763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826646160995297521817175 2739969241492946282725763)
          ·
            refine ⟨4109953862239419424088645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739969241492946282725763 4109953862239419424088645)
            ·
              refine ⟨770616349169891142016621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4109953862239419424088645 770616349169891142016621)
              ·
                refine ⟨288981130938709178256233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 770616349169891142016621 288981130938709178256233)
                ·
                  refine ⟨216735848204031883692175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288981130938709178256233 216735848204031883692175)
                  ·
                    rfl

theorem cell20_474853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_474853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474853 prefixEnd_474853 := by exact prefixLift 474853
  have htrace : WordTrace (prefixWord ++ tailWord_474853) baseStart_474853 baseEnd_474853 := by
    simpa [prefixWord, tailWord_474853, baseEnd_474853] using wordTrace_append hprefix tailTrace_474853
  have hstable : (prefixWord ++ tailWord_474853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474853).length < 2 ^ (prefixWord ++ tailWord_474853).sum := by decide
  have hdescent : baseEnd_474853 < baseStart_474853 := by decide
  rcases family_descends (prefixWord ++ tailWord_474853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474884 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_474884 : Nat := 118140960795 + 474884 * 2 ^ 59
def prefixEnd_474884 : Nat := 4983230072969 + 3 ^ 40 * 474884 * 2
def baseEnd_474884 : Nat := 216749997448733553658715

theorem tailTrace_474884 : CollatzResearch.WordTrace tailWord_474884 prefixEnd_474884 216749997448733553658715 := by
  unfold tailWord_474884
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660221205791923287655853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11546961607722564383541137 8660221205791923287655853)
  ·
    refine ⟨3247582952171971232870945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8660221205791923287655853 3247582952171971232870945)
    ·
      refine ⟨2435687214128978424653209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3247582952171971232870945 2435687214128978424653209)
      ·
        refine ⟨1826765410596733818489907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2435687214128978424653209 1826765410596733818489907)
        ·
          refine ⟨2740148115895100727734861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826765410596733818489907 2740148115895100727734861)
          ·
            refine ⟨1027555543460662772900573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2740148115895100727734861 1027555543460662772900573)
            ·
              refine ⟨385333328797748539837715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1027555543460662772900573 385333328797748539837715)
              ·
                refine ⟨577999993196622809756573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385333328797748539837715 577999993196622809756573)
                ·
                  refine ⟨216749997448733553658715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 577999993196622809756573 216749997448733553658715)
                  ·
                    rfl

theorem cell20_474884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_474884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474884 prefixEnd_474884 := by exact prefixLift 474884
  have htrace : WordTrace (prefixWord ++ tailWord_474884) baseStart_474884 baseEnd_474884 := by
    simpa [prefixWord, tailWord_474884, baseEnd_474884] using wordTrace_append hprefix tailTrace_474884
  have hstable : (prefixWord ++ tailWord_474884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474884).length < 2 ^ (prefixWord ++ tailWord_474884).sum := by decide
  have hdescent : baseEnd_474884 < baseStart_474884 := by decide
  rcases family_descends (prefixWord ++ tailWord_474884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474898 : List Nat := [3, 2, 4, 1, 1, 2, 1, 6]
def baseStart_474898 : Nat := 118140960795 + 474898 * 2 ^ 59
def prefixEnd_474898 : Nat := 4983230072969 + 3 ^ 40 * 474898 * 2
def baseEnd_474898 : Nat := 72252129143403909063997

theorem tailTrace_474898 : CollatzResearch.WordTrace tailWord_474898 prefixEnd_474898 72252129143403909063997 := by
  unfold tailWord_474898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330238258383281741580337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11547302022355417977547565 4330238258383281741580337)
  ·
    refine ⟨3247678693787461306185253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4330238258383281741580337 3247678693787461306185253)
    ·
      refine ⟨608939755085148994909735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3247678693787461306185253 608939755085148994909735)
      ·
        refine ⟨913409632627723492364603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608939755085148994909735 913409632627723492364603)
        ·
          refine ⟨1370114448941585238546905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913409632627723492364603 1370114448941585238546905)
          ·
            refine ⟨1027585836706188928910179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370114448941585238546905 1027585836706188928910179)
            ·
              refine ⟨1541378755059283393365269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027585836706188928910179 1541378755059283393365269)
              ·
                refine ⟨72252129143403909063997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1541378755059283393365269 72252129143403909063997)
                ·
                  rfl

theorem cell20_474898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_474898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474898 prefixEnd_474898 := by exact prefixLift 474898
  have htrace : WordTrace (prefixWord ++ tailWord_474898) baseStart_474898 baseEnd_474898 := by
    simpa [prefixWord, tailWord_474898, baseEnd_474898] using wordTrace_append hprefix tailTrace_474898
  have hstable : (prefixWord ++ tailWord_474898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474898).length < 2 ^ (prefixWord ++ tailWord_474898).sum := by decide
  have hdescent : baseEnd_474898 < baseStart_474898 := by decide
  rcases family_descends (prefixWord ++ tailWord_474898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474940 : List Nat := [2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_474940 : Nat := 118140960795 + 474940 * 2 ^ 59
def prefixEnd_474940 : Nat := 4983230072969 + 3 ^ 40 * 474940 * 2
def baseEnd_474940 : Nat := 72258519124882082597273

theorem tailTrace_474940 : CollatzResearch.WordTrace tailWord_474940 prefixEnd_474940 72258519124882082597273 := by
  unfold tailWord_474940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8661242449690484069675137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11548323266253978759566849 8661242449690484069675137)
  ·
    refine ⟨6495931837267863052256353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8661242449690484069675137 6495931837267863052256353)
    ·
      refine ⟨4871948877950897289192265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6495931837267863052256353 4871948877950897289192265)
      ·
        refine ⟨3653961658463172966894199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4871948877950897289192265 3653961658463172966894199)
        ·
          refine ⟨5480942487694759450341299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653961658463172966894199 5480942487694759450341299)
          ·
            refine ⟨8221413731542139175511949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480942487694759450341299 8221413731542139175511949)
            ·
              refine ⟨3083030149328302190816981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8221413731542139175511949 3083030149328302190816981)
              ·
                refine ⟨72258519124882082597273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3083030149328302190816981 72258519124882082597273)
                ·
                  rfl

theorem cell20_474940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_474940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474940 prefixEnd_474940 := by exact prefixLift 474940
  have htrace : WordTrace (prefixWord ++ tailWord_474940) baseStart_474940 baseEnd_474940 := by
    simpa [prefixWord, tailWord_474940, baseEnd_474940] using wordTrace_append hprefix tailTrace_474940
  have hstable : (prefixWord ++ tailWord_474940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474940).length < 2 ^ (prefixWord ++ tailWord_474940).sum := by decide
  have hdescent : baseEnd_474940 < baseStart_474940 := by decide
  rcases family_descends (prefixWord ++ tailWord_474940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474943 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_474943 : Nat := 118140960795 + 474943 * 2 ^ 59
def prefixEnd_474943 : Nat := 4983230072969 + 3 ^ 40 * 474943 * 2
def baseEnd_474943 : Nat := 216776926656391570691807

theorem tailTrace_474943 : CollatzResearch.WordTrace tailWord_474943 prefixEnd_474943 216776926656391570691807 := by
  unfold tailWord_474943
  simp only [CollatzResearch.WordTrace]
  refine ⟨17322594318370099651709483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11548396212246733101139655 17322594318370099651709483)
  ·
    refine ⟨25983891477555149477564225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17322594318370099651709483 25983891477555149477564225)
    ·
      refine ⟨19487918608166362108173169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25983891477555149477564225 19487918608166362108173169)
      ·
        refine ⟨14615938956124771581129877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19487918608166362108173169 14615938956124771581129877)
        ·
          refine ⟨685122138568348667865463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14615938956124771581129877 685122138568348667865463)
          ·
            refine ⟨1027683207852523001798195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685122138568348667865463 1027683207852523001798195)
            ·
              refine ⟨1541524811778784502697293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027683207852523001798195 1541524811778784502697293)
              ·
                refine ⟨578071804417044188511485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1541524811778784502697293 578071804417044188511485)
                ·
                  refine ⟨216776926656391570691807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578071804417044188511485 216776926656391570691807)
                  ·
                    rfl

theorem cell20_474943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_474943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474943 prefixEnd_474943 := by exact prefixLift 474943
  have htrace : WordTrace (prefixWord ++ tailWord_474943) baseStart_474943 baseEnd_474943 := by
    simpa [prefixWord, tailWord_474943, baseEnd_474943] using wordTrace_append hprefix tailTrace_474943
  have hstable : (prefixWord ++ tailWord_474943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474943).length < 2 ^ (prefixWord ++ tailWord_474943).sum := by decide
  have hdescent : baseEnd_474943 < baseStart_474943 := by decide
  rcases family_descends (prefixWord ++ tailWord_474943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_474985 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_474985 : Nat := 118140960795 + 474985 * 2 ^ 59
def prefixEnd_474985 : Nat := 4983230072969 + 3 ^ 40 * 474985 * 2
def baseEnd_474985 : Nat := 216796096600826091291635

theorem tailTrace_474985 : CollatzResearch.WordTrace tailWord_474985 prefixEnd_474985 216796096600826091291635 := by
  unfold tailWord_474985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17324126184217940824738409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11549417456145293883158939 17324126184217940824738409)
  ·
    refine ⟨12993094638163455618553807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17324126184217940824738409 12993094638163455618553807)
    ·
      refine ⟨19489641957245183427830711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12993094638163455618553807 19489641957245183427830711)
      ·
        refine ⟨29234462935867775141746067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19489641957245183427830711 29234462935867775141746067)
        ·
          refine ⟨43851694403801662712619101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29234462935867775141746067 43851694403801662712619101)
          ·
            refine ⟨16444385401425623517232163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43851694403801662712619101 16444385401425623517232163)
            ·
              refine ⟨24666578102138435275848245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16444385401425623517232163 24666578102138435275848245)
              ·
                refine ⟨2312491697075478307110773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24666578102138435275848245 2312491697075478307110773)
                ·
                  refine ⟨216796096600826091291635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2312491697075478307110773 216796096600826091291635)
                  ·
                    rfl

theorem cell20_474985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_474985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_474985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_474985 prefixEnd_474985 := by exact prefixLift 474985
  have htrace : WordTrace (prefixWord ++ tailWord_474985) baseStart_474985 baseEnd_474985 := by
    simpa [prefixWord, tailWord_474985, baseEnd_474985] using wordTrace_append hprefix tailTrace_474985
  have hstable : (prefixWord ++ tailWord_474985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_474985).length < 2 ^ (prefixWord ++ tailWord_474985).sum := by decide
  have hdescent : baseEnd_474985 < baseStart_474985 := by decide
  rcases family_descends (prefixWord ++ tailWord_474985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475002 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_475002 : Nat := 118140960795 + 475002 * 2 ^ 59
def prefixEnd_475002 : Nat := 4983230072969 + 3 ^ 40 * 475002 * 2
def baseEnd_475002 : Nat := 216803855864049587724899

theorem tailTrace_475002 : CollatzResearch.WordTrace tailWord_475002 prefixEnd_475002 216803855864049587724899 := by
  unfold tailWord_475002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331186556289088182026815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11549830816770901818738173 4331186556289088182026815)
  ·
    refine ⟨6496779834433632273040223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331186556289088182026815 6496779834433632273040223)
    ·
      refine ⟨9745169751650448409560335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496779834433632273040223 9745169751650448409560335)
      ·
        refine ⟨14617754627475672614340503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745169751650448409560335 14617754627475672614340503)
        ·
          refine ⟨21926631941213508921510755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14617754627475672614340503 21926631941213508921510755)
          ·
            refine ⟨32889947911820263382266133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21926631941213508921510755 32889947911820263382266133)
            ·
              refine ⟨1541716308366574846043725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32889947911820263382266133 1541716308366574846043725)
              ·
                refine ⟨578143615637465567266397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1541716308366574846043725 578143615637465567266397)
                ·
                  refine ⟨216803855864049587724899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578143615637465567266397 216803855864049587724899)
                  ·
                    rfl

theorem cell20_475002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_475002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475002 prefixEnd_475002 := by exact prefixLift 475002
  have htrace : WordTrace (prefixWord ++ tailWord_475002) baseStart_475002 baseEnd_475002 := by
    simpa [prefixWord, tailWord_475002, baseEnd_475002] using wordTrace_append hprefix tailTrace_475002
  have hstable : (prefixWord ++ tailWord_475002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475002).length < 2 ^ (prefixWord ++ tailWord_475002).sum := by decide
  have hdescent : baseEnd_475002 < baseStart_475002 := by decide
  rcases family_descends (prefixWord ++ tailWord_475002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475036 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_475036 : Nat := 118140960795 + 475036 * 2 ^ 59
def prefixEnd_475036 : Nat := 4983230072969 + 3 ^ 40 * 475036 * 2
def baseEnd_475036 : Nat := 216819374390496580591427

theorem tailTrace_475036 : CollatzResearch.WordTrace tailWord_475036 prefixEnd_475036 216819374390496580591427 := by
  unfold tailWord_475036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662993153516588267422481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11550657538022117689896641 8662993153516588267422481)
  ·
    refine ⟨6497244865137441200566861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8662993153516588267422481 6497244865137441200566861)
    ·
      refine ⟨2436466824426540450212573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6497244865137441200566861 2436466824426540450212573)
      ·
        refine ⟨913675059159952668829715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2436466824426540450212573 913675059159952668829715)
        ·
          refine ⟨1370512588739929003244573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913675059159952668829715 1370512588739929003244573)
          ·
            refine ⟨513942220777473376216715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1370512588739929003244573 513942220777473376216715)
            ·
              refine ⟨770913331166210064325073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513942220777473376216715 770913331166210064325073)
              ·
                refine ⟨578184998374657548243805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770913331166210064325073 578184998374657548243805)
                ·
                  refine ⟨216819374390496580591427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578184998374657548243805 216819374390496580591427)
                  ·
                    rfl

theorem cell20_475036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_475036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475036 prefixEnd_475036 := by exact prefixLift 475036
  have htrace : WordTrace (prefixWord ++ tailWord_475036) baseStart_475036 baseEnd_475036 := by
    simpa [prefixWord, tailWord_475036, baseEnd_475036] using wordTrace_append hprefix tailTrace_475036
  have hstable : (prefixWord ++ tailWord_475036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475036).length < 2 ^ (prefixWord ++ tailWord_475036).sum := by decide
  have hdescent : baseEnd_475036 < baseStart_475036 := by decide
  rcases family_descends (prefixWord ++ tailWord_475036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475098 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_475098 : Nat := 118140960795 + 475098 * 2 ^ 59
def prefixEnd_475098 : Nat := 4983230072969 + 3 ^ 40 * 475098 * 2
def baseEnd_475098 : Nat := 216847672879899920524507

theorem tailTrace_475098 : CollatzResearch.WordTrace tailWord_475098 prefixEnd_475098 216847672879899920524507 := by
  unfold tailWord_475098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332061908202140280900487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11552165088539040749067965 4332061908202140280900487)
  ·
    refine ⟨6498092862303210421350731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332061908202140280900487 6498092862303210421350731)
    ·
      refine ⟨9747139293454815632026097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498092862303210421350731 9747139293454815632026097)
      ·
        refine ⟨7310354470091111724019573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9747139293454815632026097 7310354470091111724019573)
        ·
          refine ⟨685345731571041724126835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7310354470091111724019573 685345731571041724126835)
          ·
            refine ⟨1028018597356562586190253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685345731571041724126835 1028018597356562586190253)
            ·
              refine ⟨385506974008710969821345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1028018597356562586190253 385506974008710969821345)
              ·
                refine ⟨289130230506533227366009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385506974008710969821345 289130230506533227366009)
                ·
                  refine ⟨216847672879899920524507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289130230506533227366009 216847672879899920524507)
                  ·
                    rfl

theorem cell20_475098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_475098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475098 prefixEnd_475098 := by exact prefixLift 475098
  have htrace : WordTrace (prefixWord ++ tailWord_475098) baseStart_475098 baseEnd_475098 := by
    simpa [prefixWord, tailWord_475098, baseEnd_475098] using wordTrace_append hprefix tailTrace_475098
  have hstable : (prefixWord ++ tailWord_475098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475098).length < 2 ^ (prefixWord ++ tailWord_475098).sum := by decide
  have hdescent : baseEnd_475098 < baseStart_475098 := by decide
  rcases family_descends (prefixWord ++ tailWord_475098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475149 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 2]
def baseStart_475149 : Nat := 118140960795 + 475149 * 2 ^ 59
def prefixEnd_475149 : Nat := 4983230072969 + 3 ^ 40 * 475149 * 2
def baseEnd_475149 : Nat := 216870950669570409824299

theorem tailTrace_475149 : CollatzResearch.WordTrace tailWord_475149 prefixEnd_475149 216870950669570409824299 := by
  unfold tailWord_475149
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330107755623796833708501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11553405170415864555805667 17330107755623796833708501)
  ·
    refine ⟨406174400522432738290043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17330107755623796833708501 406174400522432738290043)
    ·
      refine ⟨609261600783649107435065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406174400522432738290043 609261600783649107435065)
      ·
        refine ⟨456946200587736830576299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609261600783649107435065 456946200587736830576299)
        ·
          refine ⟨685419300881605245864449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456946200587736830576299 685419300881605245864449)
          ·
            refine ⟨514064475661203934398337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685419300881605245864449 514064475661203934398337)
            ·
              refine ⟨385548356745902950798753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514064475661203934398337 385548356745902950798753)
              ·
                refine ⟨289161267559427213099065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385548356745902950798753 289161267559427213099065)
                ·
                  refine ⟨216870950669570409824299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289161267559427213099065 216870950669570409824299)
                  ·
                    rfl

theorem cell20_475149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_475149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475149 prefixEnd_475149 := by exact prefixLift 475149
  have htrace : WordTrace (prefixWord ++ tailWord_475149) baseStart_475149 baseEnd_475149 := by
    simpa [prefixWord, tailWord_475149, baseEnd_475149] using wordTrace_append hprefix tailTrace_475149
  have hstable : (prefixWord ++ tailWord_475149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475149).length < 2 ^ (prefixWord ++ tailWord_475149).sum := by decide
  have hdescent : baseEnd_475149 < baseStart_475149 := by decide
  rcases family_descends (prefixWord ++ tailWord_475149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475157 : List Nat := [1, 3, 2, 1, 5, 1, 1, 4, 2]
def baseStart_475157 : Nat := 118140960795 + 475157 * 2 ^ 59
def prefixEnd_475157 : Nat := 4983230072969 + 3 ^ 40 * 475157 * 2
def baseEnd_475157 : Nat := 216874602087557937557599

theorem tailTrace_475157 : CollatzResearch.WordTrace tailWord_475157 prefixEnd_475157 216874602087557937557599 := by
  unfold tailWord_475157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330399539594814199999725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11553599693063209466666483 17330399539594814199999725)
  ·
    refine ⟨6498899827348055324999897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17330399539594814199999725 6498899827348055324999897)
    ·
      refine ⟨4874174870511041493749923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6498899827348055324999897 4874174870511041493749923)
      ·
        refine ⟨7311262305766562240624885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874174870511041493749923 7311262305766562240624885)
        ·
          refine ⟨685430841165615210058583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7311262305766562240624885 685430841165615210058583)
          ·
            refine ⟨1028146261748422815087875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685430841165615210058583 1028146261748422815087875)
            ·
              refine ⟨1542219392622634222631813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028146261748422815087875 1542219392622634222631813)
              ·
                refine ⟨289166136116743916743465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1542219392622634222631813 289166136116743916743465)
                ·
                  refine ⟨216874602087557937557599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289166136116743916743465 216874602087557937557599)
                  ·
                    rfl

theorem cell20_475157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_475157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475157 prefixEnd_475157 := by exact prefixLift 475157
  have htrace : WordTrace (prefixWord ++ tailWord_475157) baseStart_475157 baseEnd_475157 := by
    simpa [prefixWord, tailWord_475157, baseEnd_475157] using wordTrace_append hprefix tailTrace_475157
  have hstable : (prefixWord ++ tailWord_475157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475157).length < 2 ^ (prefixWord ++ tailWord_475157).sum := by decide
  have hdescent : baseEnd_475157 < baseStart_475157 := by decide
  rcases family_descends (prefixWord ++ tailWord_475157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475178 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_475178 : Nat := 118140960795 + 475178 * 2 ^ 59
def prefixEnd_475178 : Nat := 4983230072969 + 3 ^ 40 * 475178 * 2
def baseEnd_475178 : Nat := 216884187059775197857513

theorem tailTrace_475178 : CollatzResearch.WordTrace tailWord_475178 prefixEnd_475178 216884187059775197857513 := by
  unfold tailWord_475178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332791368129683696628547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11554110315012489857676125 4332791368129683696628547)
  ·
    refine ⟨6499187052194525544942821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4332791368129683696628547 6499187052194525544942821)
    ·
      refine ⟨1218597572286473539676779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6499187052194525544942821 1218597572286473539676779)
      ·
        refine ⟨1827896358429710309515169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218597572286473539676779 1827896358429710309515169)
        ·
          refine ⟨1370922268822282732136377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827896358429710309515169 1370922268822282732136377)
          ·
            refine ⟨1028191701616712049102283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370922268822282732136377 1028191701616712049102283)
            ·
              refine ⟨1542287552425068073653425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028191701616712049102283 1542287552425068073653425)
              ·
                refine ⟨1156715664318801055240069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542287552425068073653425 1156715664318801055240069)
                ·
                  refine ⟨216884187059775197857513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1156715664318801055240069 216884187059775197857513)
                  ·
                    rfl

theorem cell20_475178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_475178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475178 prefixEnd_475178 := by exact prefixLift 475178
  have htrace : WordTrace (prefixWord ++ tailWord_475178) baseStart_475178 baseEnd_475178 := by
    simpa [prefixWord, tailWord_475178, baseEnd_475178] using wordTrace_append hprefix tailTrace_475178
  have hstable : (prefixWord ++ tailWord_475178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475178).length < 2 ^ (prefixWord ++ tailWord_475178).sum := by decide
  have hdescent : baseEnd_475178 < baseStart_475178 := by decide
  rcases family_descends (prefixWord ++ tailWord_475178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_475185 : List Nat := [1, 2, 2, 3, 1, 4, 3, 4]
def baseStart_475185 : Nat := 118140960795 + 475185 * 2 ^ 59
def prefixEnd_475185 : Nat := 4983230072969 + 3 ^ 40 * 475185 * 2
def baseEnd_475185 : Nat := 72295794016838094874717

theorem tailTrace_475185 : CollatzResearch.WordTrace tailWord_475185 prefixEnd_475185 72295794016838094874717 := by
  unfold tailWord_475185
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331420783493374982019009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11554280522328916654679339 17331420783493374982019009)
  ·
    refine ⟨12998565587620031236514257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17331420783493374982019009 12998565587620031236514257)
    ·
      refine ⟨9748924190715023427385693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12998565587620031236514257 9748924190715023427385693)
      ·
        refine ⟨3655846571518133785269635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9748924190715023427385693 3655846571518133785269635)
        ·
          refine ⟨5483769857277200677904453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655846571518133785269635 5483769857277200677904453)
          ·
            refine ⟨1028206848239475127107085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5483769857277200677904453 1028206848239475127107085)
            ·
              refine ⟨385577568089803172665157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1028206848239475127107085 385577568089803172665157)
              ·
                refine ⟨72295794016838094874717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385577568089803172665157 72295794016838094874717)
                ·
                  rfl

theorem cell20_475185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_475185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_475185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_475185 prefixEnd_475185 := by exact prefixLift 475185
  have htrace : WordTrace (prefixWord ++ tailWord_475185) baseStart_475185 baseEnd_475185 := by
    simpa [prefixWord, tailWord_475185, baseEnd_475185] using wordTrace_append hprefix tailTrace_475185
  have hstable : (prefixWord ++ tailWord_475185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_475185).length < 2 ^ (prefixWord ++ tailWord_475185).sum := by decide
  have hdescent : baseEnd_475185 < baseStart_475185 := by decide
  rcases family_descends (prefixWord ++ tailWord_475185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
