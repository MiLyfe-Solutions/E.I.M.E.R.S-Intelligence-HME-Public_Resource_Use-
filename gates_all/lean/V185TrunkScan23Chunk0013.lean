import V185TrunkScan23Chunk0012

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_76099 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 1, 5, 2]
def baseStart_76099 : Nat := 118140960795 + 76099 * 2 ^ 59
def prefixEnd_76099 : Nat := 4983230072969 + 3 ^ 40 * 76099 * 2
def baseEnd_76099 : Nat := 39075364326602996012533

theorem tailTrace_76099 : CollatzResearch.WordTrace tailWord_76099 prefixEnd_76099 39075364326602996012533 := by
  unfold tailWord_76099
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775558551313794519591351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1850372367542529679727567 2775558551313794519591351)
  ·
    refine ⟨4163337826970691779387027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2775558551313794519591351 4163337826970691779387027)
    ·
      refine ⟨6245006740456037669080541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163337826970691779387027 6245006740456037669080541)
      ·
        refine ⟨2341877527671014125905203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6245006740456037669080541 2341877527671014125905203)
        ·
          refine ⟨3512816291506521188857805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341877527671014125905203 3512816291506521188857805)
          ·
            refine ⟨1317306109314945445821677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3512816291506521188857805 1317306109314945445821677)
            ·
              refine ⟨493989790993104542183129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1317306109314945445821677 493989790993104542183129)
              ·
                refine ⟨370492343244828406637347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493989790993104542183129 370492343244828406637347)
                ·
                  refine ⟨555738514867242609956021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370492343244828406637347 555738514867242609956021)
                  ·
                    refine ⟨52100485768803994683377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 555738514867242609956021 52100485768803994683377)
                    ·
                      refine ⟨39075364326602996012533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52100485768803994683377 39075364326602996012533)
                      ·
                        rfl

theorem cell23_76099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_76099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76099 prefixEnd_76099 := by exact prefixLift 76099
  have htrace : WordTrace (prefixWord ++ tailWord_76099) baseStart_76099 baseEnd_76099 := by
    simpa [prefixWord, tailWord_76099, baseEnd_76099] using wordTrace_append hprefix tailTrace_76099
  have hstable : (prefixWord ++ tailWord_76099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76099).length < 2 ^ (prefixWord ++ tailWord_76099).sum := by decide
  have hdescent : baseEnd_76099 < baseStart_76099 := by decide
  rcases family_descends (prefixWord ++ tailWord_76099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76116 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_76116 : Nat := 118140960795 + 76116 * 2 ^ 59
def prefixEnd_76116 : Nat := 4983230072969 + 3 ^ 40 * 76116 * 2
def baseEnd_76116 : Nat := 39084093497729429499955

theorem tailTrace_76116 : CollatzResearch.WordTrace tailWord_76116 prefixEnd_76116 39084093497729429499955 := by
  unfold tailWord_76116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388089296126103211480101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1850785728168137615306801 1388089296126103211480101)
  ·
    refine ⟨260266743023644352152519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1388089296126103211480101 260266743023644352152519)
    ·
      refine ⟨390400114535466528228779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260266743023644352152519 390400114535466528228779)
      ·
        refine ⟨585600171803199792343169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390400114535466528228779 585600171803199792343169)
        ·
          refine ⟨439200128852399844257377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585600171803199792343169 439200128852399844257377)
          ·
            refine ⟨329400096639299883193033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439200128852399844257377 329400096639299883193033)
            ·
              refine ⟨247050072479474912394775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329400096639299883193033 247050072479474912394775)
              ·
                refine ⟨370575108719212368592163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247050072479474912394775 370575108719212368592163)
                ·
                  refine ⟨555862663078818552888245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370575108719212368592163 555862663078818552888245)
                  ·
                    refine ⟨52112124663639239333273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 555862663078818552888245 52112124663639239333273)
                    ·
                      refine ⟨39084093497729429499955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52112124663639239333273 39084093497729429499955)
                      ·
                        rfl

theorem cell23_76116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_76116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76116 prefixEnd_76116 := by exact prefixLift 76116
  have htrace : WordTrace (prefixWord ++ tailWord_76116) baseStart_76116 baseEnd_76116 := by
    simpa [prefixWord, tailWord_76116, baseEnd_76116] using wordTrace_append hprefix tailTrace_76116
  have hstable : (prefixWord ++ tailWord_76116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76116).length < 2 ^ (prefixWord ++ tailWord_76116).sum := by decide
  have hdescent : baseEnd_76116 < baseStart_76116 := by decide
  rcases family_descends (prefixWord ++ tailWord_76116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76122 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_76122 : Nat := 118140960795 + 76122 * 2 ^ 59
def prefixEnd_76122 : Nat := 4983230072969 + 3 ^ 40 * 76122 * 2
def baseEnd_76122 : Nat := 13029058127218802008309

theorem tailTrace_76122 : CollatzResearch.WordTrace tailWord_76122 prefixEnd_76122 13029058127218802008309 := by
  unfold tailWord_76122
  simp only [CollatzResearch.WordTrace]
  refine ⟨694099357557617361919655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1850931620153646298452413 694099357557617361919655)
  ·
    refine ⟨1041149036336426042879483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 694099357557617361919655 1041149036336426042879483)
    ·
      refine ⟨1561723554504639064319225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041149036336426042879483 1561723554504639064319225)
      ·
        refine ⟨1171292665878479298239419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1561723554504639064319225 1171292665878479298239419)
        ·
          refine ⟨1756938998817718947359129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171292665878479298239419 1756938998817718947359129)
          ·
            refine ⟨1317704249113289210519347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756938998817718947359129 1317704249113289210519347)
            ·
              refine ⟨1976556373669933815779021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317704249113289210519347 1976556373669933815779021)
              ·
                refine ⟨741208640126225180917133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1976556373669933815779021 741208640126225180917133)
                ·
                  refine ⟨277953240047334442843925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741208640126225180917133 277953240047334442843925)
                  ·
                    refine ⟨13029058127218802008309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 277953240047334442843925 13029058127218802008309)
                    ·
                      rfl

theorem cell23_76122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_76122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76122 prefixEnd_76122 := by exact prefixLift 76122
  have htrace : WordTrace (prefixWord ++ tailWord_76122) baseStart_76122 baseEnd_76122 := by
    simpa [prefixWord, tailWord_76122, baseEnd_76122] using wordTrace_append hprefix tailTrace_76122
  have hstable : (prefixWord ++ tailWord_76122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76122).length < 2 ^ (prefixWord ++ tailWord_76122).sum := by decide
  have hdescent : baseEnd_76122 < baseStart_76122 := by decide
  rcases family_descends (prefixWord ++ tailWord_76122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76140 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 3, 1, 3]
def baseStart_76140 : Nat := 118140960795 + 76140 * 2 ^ 59
def prefixEnd_76140 : Nat := 4983230072969 + 3 ^ 40 * 76140 * 2
def baseEnd_76140 : Nat := 39096417033437335599845

theorem tailTrace_76140 : CollatzResearch.WordTrace tailWord_76140 prefixEnd_76140 39096417033437335599845 := by
  unfold tailWord_76140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388526972082629260916937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1851369296110172347889249 1388526972082629260916937)
  ·
    refine ⟨1041395229061971945687703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1388526972082629260916937 1041395229061971945687703)
    ·
      refine ⟨1562092843592957918531555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041395229061971945687703 1562092843592957918531555)
      ·
        refine ⟨2343139265389436877797333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562092843592957918531555 2343139265389436877797333)
        ·
          refine ⟨54917326532564926823375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2343139265389436877797333 54917326532564926823375)
          ·
            refine ⟨82375989798847390235063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54917326532564926823375 82375989798847390235063)
            ·
              refine ⟨123563984698271085352595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82375989798847390235063 123563984698271085352595)
              ·
                refine ⟨185345977047406628028893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123563984698271085352595 185345977047406628028893)
                ·
                  refine ⟨69504741392777485510835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185345977047406628028893 69504741392777485510835)
                  ·
                    refine ⟨104257112089166228266253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69504741392777485510835 104257112089166228266253)
                    ·
                      refine ⟨39096417033437335599845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 104257112089166228266253 39096417033437335599845)
                      ·
                        rfl

theorem cell23_76140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_76140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76140 prefixEnd_76140 := by exact prefixLift 76140
  have htrace : WordTrace (prefixWord ++ tailWord_76140) baseStart_76140 baseEnd_76140 := by
    simpa [prefixWord, tailWord_76140, baseEnd_76140] using wordTrace_append hprefix tailTrace_76140
  have hstable : (prefixWord ++ tailWord_76140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76140).length < 2 ^ (prefixWord ++ tailWord_76140).sum := by decide
  have hdescent : baseEnd_76140 < baseStart_76140 := by decide
  rcases family_descends (prefixWord ++ tailWord_76140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76163 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 4]
def baseStart_76163 : Nat := 118140960795 + 76163 * 2 ^ 59
def prefixEnd_76163 : Nat := 4983230072969 + 3 ^ 40 * 76163 * 2
def baseEnd_76163 : Nat := 39108227088490745612239

theorem tailTrace_76163 : CollatzResearch.WordTrace tailWord_76163 prefixEnd_76163 39108227088490745612239 := by
  unfold tailWord_76163
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777892823081933449921143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1851928548721288966614095 2777892823081933449921143)
  ·
    refine ⟨4166839234622900174881715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777892823081933449921143 4166839234622900174881715)
    ·
      refine ⟨6250258851934350262322573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166839234622900174881715 6250258851934350262322573)
      ·
        refine ⟨2343847069475381348370965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6250258851934350262322573 2343847069475381348370965)
        ·
          refine ⟨109867831381658500704889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2343847069475381348370965 109867831381658500704889)
          ·
            refine ⟨82400873536243875528667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109867831381658500704889 82400873536243875528667)
            ·
              refine ⟨123601310304365813293001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82400873536243875528667 123601310304365813293001)
              ·
                refine ⟨92700982728274359969751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123601310304365813293001 92700982728274359969751)
                ·
                  refine ⟨139051474092411539954627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92700982728274359969751 139051474092411539954627)
                  ·
                    refine ⟨208577211138617309931941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139051474092411539954627 208577211138617309931941)
                    ·
                      refine ⟨39108227088490745612239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 208577211138617309931941 39108227088490745612239)
                      ·
                        rfl

theorem cell23_76163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_76163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76163 prefixEnd_76163 := by exact prefixLift 76163
  have htrace : WordTrace (prefixWord ++ tailWord_76163) baseStart_76163 baseEnd_76163 := by
    simpa [prefixWord, tailWord_76163, baseEnd_76163] using wordTrace_append hprefix tailTrace_76163
  have hstable : (prefixWord ++ tailWord_76163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76163).length < 2 ^ (prefixWord ++ tailWord_76163).sum := by decide
  have hdescent : baseEnd_76163 < baseStart_76163 := by decide
  rcases family_descends (prefixWord ++ tailWord_76163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76180 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_76180 : Nat := 118140960795 + 76180 * 2 ^ 59
def prefixEnd_76180 : Nat := 4983230072969 + 3 ^ 40 * 76180 * 2
def baseEnd_76180 : Nat := 39116956259617179099661

theorem tailTrace_76180 : CollatzResearch.WordTrace tailWord_76180 prefixEnd_76180 39116956259617179099661 := by
  unfold tailWord_76180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1389256432010172676644997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1852341909346896902193329 1389256432010172676644997)
  ·
    refine ⟨260485581001907376870937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1389256432010172676644997 260485581001907376870937)
    ·
      refine ⟨195364185751430532653203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260485581001907376870937 195364185751430532653203)
      ·
        refine ⟨293046278627145798979805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195364185751430532653203 293046278627145798979805)
        ·
          refine ⟨109892354485179674617427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293046278627145798979805 109892354485179674617427)
          ·
            refine ⟨164838531727769511926141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109892354485179674617427 164838531727769511926141)
            ·
              refine ⟨61814449397913566972303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164838531727769511926141 61814449397913566972303)
              ·
                refine ⟨92721674096870350458455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61814449397913566972303 92721674096870350458455)
                ·
                  refine ⟨139082511145305525687683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92721674096870350458455 139082511145305525687683)
                  ·
                    refine ⟨208623766717958288531525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139082511145305525687683 208623766717958288531525)
                    ·
                      refine ⟨39116956259617179099661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 208623766717958288531525 39116956259617179099661)
                      ·
                        rfl

theorem cell23_76180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_76180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76180 prefixEnd_76180 := by exact prefixLift 76180
  have htrace : WordTrace (prefixWord ++ tailWord_76180) baseStart_76180 baseEnd_76180 := by
    simpa [prefixWord, tailWord_76180, baseEnd_76180] using wordTrace_append hprefix tailTrace_76180
  have hstable : (prefixWord ++ tailWord_76180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76180).length < 2 ^ (prefixWord ++ tailWord_76180).sum := by decide
  have hdescent : baseEnd_76180 < baseStart_76180 := by decide
  rcases family_descends (prefixWord ++ tailWord_76180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76190 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_76190 : Nat := 118140960795 + 76190 * 2 ^ 59
def prefixEnd_76190 : Nat := 4983230072969 + 3 ^ 40 * 76190 * 2
def baseEnd_76190 : Nat := 13040697022054046658205

theorem tailTrace_76190 : CollatzResearch.WordTrace tailWord_76190 prefixEnd_76190 13040697022054046658205 := by
  unfold tailWord_76190
  simp only [CollatzResearch.WordTrace]
  refine ⟨347359699248014632644253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1852585062656078040769349 347359699248014632644253)
  ·
    refine ⟨130259887218005487241595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 347359699248014632644253 130259887218005487241595)
    ·
      refine ⟨195389830827008230862393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130259887218005487241595 195389830827008230862393)
      ·
        refine ⟨146542373120256173146795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195389830827008230862393 146542373120256173146795)
        ·
          refine ⟨219813559680384259720193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146542373120256173146795 219813559680384259720193)
          ·
            refine ⟨164860169760288194790145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219813559680384259720193 164860169760288194790145)
            ·
              refine ⟨123645127320216146092609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164860169760288194790145 123645127320216146092609)
              ·
                refine ⟨92733845490162109569457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123645127320216146092609 92733845490162109569457)
                ·
                  refine ⟨69550384117621582177093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92733845490162109569457 69550384117621582177093)
                  ·
                    refine ⟨13040697022054046658205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69550384117621582177093 13040697022054046658205)
                    ·
                      rfl

theorem cell23_76190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_76190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76190 prefixEnd_76190 := by exact prefixLift 76190
  have htrace : WordTrace (prefixWord ++ tailWord_76190) baseStart_76190 baseEnd_76190 := by
    simpa [prefixWord, tailWord_76190, baseEnd_76190] using wordTrace_append hprefix tailTrace_76190
  have hstable : (prefixWord ++ tailWord_76190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76190).length < 2 ^ (prefixWord ++ tailWord_76190).sum := by decide
  have hdescent : baseEnd_76190 < baseStart_76190 := by decide
  rcases family_descends (prefixWord ++ tailWord_76190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76196 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_76196 : Nat := 118140960795 + 76196 * 2 ^ 59
def prefixEnd_76196 : Nat := 4983230072969 + 3 ^ 40 * 76196 * 2
def baseEnd_76196 : Nat := 39125171950089116499587

theorem tailTrace_76196 : CollatzResearch.WordTrace tailWord_76196 prefixEnd_76196 39125171950089116499587 := by
  unfold tailWord_76196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1389548215981190042936221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1852730954641586723914961 1389548215981190042936221)
  ·
    refine ⟨521080580992946266101083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1389548215981190042936221 521080580992946266101083)
    ·
      refine ⟨781620871489419399151625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521080580992946266101083 781620871489419399151625)
      ·
        refine ⟨586215653617064549363719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781620871489419399151625 586215653617064549363719)
        ·
          refine ⟨879323480425596824045579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586215653617064549363719 879323480425596824045579)
          ·
            refine ⟨1318985220638395236068369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879323480425596824045579 1318985220638395236068369)
            ·
              refine ⟨989238915478796427051277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318985220638395236068369 989238915478796427051277)
              ·
                refine ⟨370964593304548660144229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 989238915478796427051277 370964593304548660144229)
                ·
                  refine ⟨69555861244602873777043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370964593304548660144229 69555861244602873777043)
                  ·
                    refine ⟨104333791866904310665565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69555861244602873777043 104333791866904310665565)
                    ·
                      refine ⟨39125171950089116499587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 104333791866904310665565 39125171950089116499587)
                      ·
                        rfl

theorem cell23_76196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_76196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76196 prefixEnd_76196 := by exact prefixLift 76196
  have htrace : WordTrace (prefixWord ++ tailWord_76196) baseStart_76196 baseEnd_76196 := by
    simpa [prefixWord, tailWord_76196, baseEnd_76196] using wordTrace_append hprefix tailTrace_76196
  have hstable : (prefixWord ++ tailWord_76196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76196).length < 2 ^ (prefixWord ++ tailWord_76196).sum := by decide
  have hdescent : baseEnd_76196 < baseStart_76196 := by decide
  rcases family_descends (prefixWord ++ tailWord_76196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76199 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 2, 7]
def baseStart_76199 : Nat := 118140960795 + 76199 * 2 ^ 59
def prefixEnd_76199 : Nat := 4983230072969 + 3 ^ 40 * 76199 * 2
def baseEnd_76199 : Nat := 13042237464017534920691

theorem tailTrace_76199 : CollatzResearch.WordTrace tailWord_76199 prefixEnd_76199 13042237464017534920691 := by
  unfold tailWord_76199
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779205850951511598231651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1852803900634341065487767 2779205850951511598231651)
  ·
    refine ⟨4168808776427267397347477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2779205850951511598231651 4168808776427267397347477)
    ·
      refine ⟨195412911395028159250663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4168808776427267397347477 195412911395028159250663)
      ·
        refine ⟨293119367092542238875995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195412911395028159250663 293119367092542238875995)
        ·
          refine ⟨439679050638813358313993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293119367092542238875995 439679050638813358313993)
          ·
            refine ⟨329759287979110018735495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439679050638813358313993 329759287979110018735495)
            ·
              refine ⟨494638931968665028103243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329759287979110018735495 494638931968665028103243)
              ·
                refine ⟨741958397952997542154865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494638931968665028103243 741958397952997542154865)
                ·
                  refine ⟨556468798464748156616149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 741958397952997542154865 556468798464748156616149)
                  ·
                    refine ⟨13042237464017534920691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 556468798464748156616149 13042237464017534920691)
                    ·
                      rfl

theorem cell23_76199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_76199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76199 prefixEnd_76199 := by exact prefixLift 76199
  have htrace : WordTrace (prefixWord ++ tailWord_76199) baseStart_76199 baseEnd_76199 := by
    simpa [prefixWord, tailWord_76199, baseEnd_76199] using wordTrace_append hprefix tailTrace_76199
  have hstable : (prefixWord ++ tailWord_76199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76199).length < 2 ^ (prefixWord ++ tailWord_76199).sum := by decide
  have hdescent : baseEnd_76199 < baseStart_76199 := by decide
  rcases family_descends (prefixWord ++ tailWord_76199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76213 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_76213 : Nat := 118140960795 + 76213 * 2 ^ 59
def prefixEnd_76213 : Nat := 4983230072969 + 3 ^ 40 * 76213 * 2
def baseEnd_76213 : Nat := 39133901121215549987009

theorem tailTrace_76213 : CollatzResearch.WordTrace tailWord_76213 prefixEnd_76213 39133901121215549987009 := by
  unfold tailWord_76213
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779716472900791989241293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1853144315267194659494195 2779716472900791989241293)
  ·
    refine ⟨1042393677337796995965485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2779716472900791989241293 1042393677337796995965485)
    ·
      refine ⟨390897629001673873487057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1042393677337796995965485 390897629001673873487057)
      ·
        refine ⟨293173221751255405115293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390897629001673873487057 293173221751255405115293)
        ·
          refine ⟨109939958156720776918235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293173221751255405115293 109939958156720776918235)
          ·
            refine ⟨164909937235081165377353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109939958156720776918235 164909937235081165377353)
            ·
              refine ⟨123682452926310874033015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164909937235081165377353 123682452926310874033015)
              ·
                refine ⟨185523679389466311049523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123682452926310874033015 185523679389466311049523)
                ·
                  refine ⟨278285519084199466574285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185523679389466311049523 278285519084199466574285)
                  ·
                    refine ⟨104357069656574799965357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278285519084199466574285 104357069656574799965357)
                    ·
                      refine ⟨39133901121215549987009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 104357069656574799965357 39133901121215549987009)
                      ·
                        rfl

theorem cell23_76213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_76213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76213 prefixEnd_76213 := by exact prefixLift 76213
  have htrace : WordTrace (prefixWord ++ tailWord_76213) baseStart_76213 baseEnd_76213 := by
    simpa [prefixWord, tailWord_76213, baseEnd_76213] using wordTrace_append hprefix tailTrace_76213
  have hstable : (prefixWord ++ tailWord_76213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76213).length < 2 ^ (prefixWord ++ tailWord_76213).sum := by decide
  have hdescent : baseEnd_76213 < baseStart_76213 := by decide
  rcases family_descends (prefixWord ++ tailWord_76213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76246 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_76246 : Nat := 118140960795 + 76246 * 2 ^ 59
def prefixEnd_76246 : Nat := 4983230072969 + 3 ^ 40 * 76246 * 2
def baseEnd_76246 : Nat := 13050281994271306958119

theorem tailTrace_76246 : CollatzResearch.WordTrace tailWord_76246 prefixEnd_76246 13050281994271306958119 := by
  unfold tailWord_76246
  simp only [CollatzResearch.WordTrace]
  refine ⟨173807505111327414074537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1853946721187492416795061 173807505111327414074537)
  ·
    refine ⟨130355628833495560555903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 173807505111327414074537 130355628833495560555903)
    ·
      refine ⟨195533443250243340833855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130355628833495560555903 195533443250243340833855)
      ·
        refine ⟨293300164875365011250783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195533443250243340833855 293300164875365011250783)
        ·
          refine ⟨439950247313047516876175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293300164875365011250783 439950247313047516876175)
          ·
            refine ⟨659925370969571275314263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439950247313047516876175 659925370969571275314263)
            ·
              refine ⟨989888056454356912971395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659925370969571275314263 989888056454356912971395)
              ·
                refine ⟨1484832084681535369457093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989888056454356912971395 1484832084681535369457093)
                ·
                  refine ⟨278406015877787881773205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484832084681535369457093 278406015877787881773205)
                  ·
                    refine ⟨13050281994271306958119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 278406015877787881773205 13050281994271306958119)
                    ·
                      rfl

theorem cell23_76246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_76246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76246 prefixEnd_76246 := by exact prefixLift 76246
  have htrace : WordTrace (prefixWord ++ tailWord_76246) baseStart_76246 baseEnd_76246 := by
    simpa [prefixWord, tailWord_76246, baseEnd_76246] using wordTrace_append hprefix tailTrace_76246
  have hstable : (prefixWord ++ tailWord_76246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76246).length < 2 ^ (prefixWord ++ tailWord_76246).sum := by decide
  have hdescent : baseEnd_76246 < baseStart_76246 := by decide
  rcases family_descends (prefixWord ++ tailWord_76246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76249 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_76249 : Nat := 118140960795 + 76249 * 2 ^ 59
def prefixEnd_76249 : Nat := 4983230072969 + 3 ^ 40 * 76249 * 2
def baseEnd_76249 : Nat := 39152386424777409136843

theorem tailTrace_76249 : CollatzResearch.WordTrace tailWord_76249 prefixEnd_76249 39152386424777409136843 := by
  unfold tailWord_76249
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781029500770370137551801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1854019667180246758367867 2781029500770370137551801)
  ·
    refine ⟨2085772125577777603163851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2781029500770370137551801 2085772125577777603163851)
    ·
      refine ⟨3128658188366666404745777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085772125577777603163851 3128658188366666404745777)
      ·
        refine ⟨2346493641274999803559333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3128658188366666404745777 2346493641274999803559333)
        ·
          refine ⟨439967557739062463167375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2346493641274999803559333 439967557739062463167375)
          ·
            refine ⟨659951336608593694751063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439967557739062463167375 659951336608593694751063)
            ·
              refine ⟨989927004912890542126595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659951336608593694751063 989927004912890542126595)
              ·
                refine ⟨1484890507369335813189893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989927004912890542126595 1484890507369335813189893)
                ·
                  refine ⟨278416970131750464973105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484890507369335813189893 278416970131750464973105)
                  ·
                    refine ⟨208812727598812848729829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 278416970131750464973105 208812727598812848729829)
                    ·
                      refine ⟨39152386424777409136843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 208812727598812848729829 39152386424777409136843)
                      ·
                        rfl

theorem cell23_76249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_76249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76249 prefixEnd_76249 := by exact prefixLift 76249
  have htrace : WordTrace (prefixWord ++ tailWord_76249) baseStart_76249 baseEnd_76249 := by
    simpa [prefixWord, tailWord_76249, baseEnd_76249] using wordTrace_append hprefix tailTrace_76249
  have hstable : (prefixWord ++ tailWord_76249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76249).length < 2 ^ (prefixWord ++ tailWord_76249).sum := by decide
  have hdescent : baseEnd_76249 < baseStart_76249 := by decide
  rcases family_descends (prefixWord ++ tailWord_76249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76266 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_76266 : Nat := 118140960795 + 76266 * 2 ^ 59
def prefixEnd_76266 : Nat := 4983230072969 + 3 ^ 40 * 76266 * 2
def baseEnd_76266 : Nat := 39161115595903842624265

theorem tailTrace_76266 : CollatzResearch.WordTrace tailWord_76266 prefixEnd_76266 39161115595903842624265 := by
  unfold tailWord_76266
  simp only [CollatzResearch.WordTrace]
  refine ⟨695412385427195510230163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1854433027805854693947101 695412385427195510230163)
  ·
    refine ⟨1043118578140793265345245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 695412385427195510230163 1043118578140793265345245)
    ·
      refine ⟨391169466802797474504467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1043118578140793265345245 391169466802797474504467)
      ·
        refine ⟨586754200204196211756701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391169466802797474504467 586754200204196211756701)
        ·
          refine ⟨220032825076573579408763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 586754200204196211756701 220032825076573579408763)
          ·
            refine ⟨330049237614860369113145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220032825076573579408763 330049237614860369113145)
            ·
              refine ⟨247536928211145276834859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330049237614860369113145 247536928211145276834859)
              ·
                refine ⟨371305392316717915252289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247536928211145276834859 371305392316717915252289)
                ·
                  refine ⟨278479044237538436439217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371305392316717915252289 278479044237538436439217)
                  ·
                    refine ⟨208859283178153827329413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 278479044237538436439217 208859283178153827329413)
                    ·
                      refine ⟨39161115595903842624265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 208859283178153827329413 39161115595903842624265)
                      ·
                        rfl

theorem cell23_76266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_76266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76266 prefixEnd_76266 := by exact prefixLift 76266
  have htrace : WordTrace (prefixWord ++ tailWord_76266) baseStart_76266 baseEnd_76266 := by
    simpa [prefixWord, tailWord_76266, baseEnd_76266] using wordTrace_append hprefix tailTrace_76266
  have hstable : (prefixWord ++ tailWord_76266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76266).length < 2 ^ (prefixWord ++ tailWord_76266).sum := by decide
  have hdescent : baseEnd_76266 < baseStart_76266 := by decide
  rcases family_descends (prefixWord ++ tailWord_76266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76270 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_76270 : Nat := 118140960795 + 76270 * 2 ^ 59
def prefixEnd_76270 : Nat := 4983230072969 + 3 ^ 40 * 76270 * 2
def baseEnd_76270 : Nat := 39163169518521826974247

theorem tailTrace_76270 : CollatzResearch.WordTrace tailWord_76270 prefixEnd_76270 39163169518521826974247 := by
  unfold tailWord_76270
  simp only [CollatzResearch.WordTrace]
  refine ⟨347724429211786340508283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1854530289129527149377509 347724429211786340508283)
  ·
    refine ⟨521586643817679510762425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347724429211786340508283 521586643817679510762425)
    ·
      refine ⟨391189982863259633071819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 521586643817679510762425 391189982863259633071819)
      ·
        refine ⟨586784974294889449607729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391189982863259633071819 586784974294889449607729)
        ·
          refine ⟨440088730721167087205797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586784974294889449607729 440088730721167087205797)
          ·
            refine ⟨82516637010218828851087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 440088730721167087205797 82516637010218828851087)
            ·
              refine ⟨123774955515328243276631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82516637010218828851087 123774955515328243276631)
              ·
                refine ⟨185662433272992364914947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123774955515328243276631 185662433272992364914947)
                ·
                  refine ⟨278493649909488547372421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185662433272992364914947 278493649909488547372421)
                  ·
                    refine ⟨52217559358029102632329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278493649909488547372421 52217559358029102632329)
                    ·
                      refine ⟨39163169518521826974247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52217559358029102632329 39163169518521826974247)
                      ·
                        rfl

theorem cell23_76270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_76270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76270 prefixEnd_76270 := by exact prefixLift 76270
  have htrace : WordTrace (prefixWord ++ tailWord_76270) baseStart_76270 baseEnd_76270 := by
    simpa [prefixWord, tailWord_76270, baseEnd_76270] using wordTrace_append hprefix tailTrace_76270
  have hstable : (prefixWord ++ tailWord_76270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76270).length < 2 ^ (prefixWord ++ tailWord_76270).sum := by decide
  have hdescent : baseEnd_76270 < baseStart_76270 := by decide
  rcases family_descends (prefixWord ++ tailWord_76270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76296 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_76296 : Nat := 118140960795 + 76296 * 2 ^ 59
def prefixEnd_76296 : Nat := 4983230072969 + 3 ^ 40 * 76296 * 2
def baseEnd_76296 : Nat := 39176520015538725249127

theorem tailTrace_76296 : CollatzResearch.WordTrace tailWord_76296 prefixEnd_76296 39176520015538725249127 := by
  unfold tailWord_76296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391371865800048582256371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1855162487733398109675161 1391371865800048582256371)
  ·
    refine ⟨2087057798700072873384557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1391371865800048582256371 2087057798700072873384557)
    ·
      refine ⟨782646674512527327519209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2087057798700072873384557 782646674512527327519209)
      ·
        refine ⟨586985005884395495639407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782646674512527327519209 586985005884395495639407)
        ·
          refine ⟨880477508826593243459111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586985005884395495639407 880477508826593243459111)
          ·
            refine ⟨1320716263239889865188667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880477508826593243459111 1320716263239889865188667)
            ·
              refine ⟨1981074394859834797783001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320716263239889865188667 1981074394859834797783001)
              ·
                refine ⟨1485805796144876098337251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1981074394859834797783001 1485805796144876098337251)
                ·
                  refine ⟨2228708694217314147505877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485805796144876098337251 2228708694217314147505877)
                  ·
                    refine ⟨52235360020718300332169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2228708694217314147505877 52235360020718300332169)
                    ·
                      refine ⟨39176520015538725249127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52235360020718300332169 39176520015538725249127)
                      ·
                        rfl

theorem cell23_76296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_76296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76296 prefixEnd_76296 := by exact prefixLift 76296
  have htrace : WordTrace (prefixWord ++ tailWord_76296) baseStart_76296 baseEnd_76296 := by
    simpa [prefixWord, tailWord_76296, baseEnd_76296] using wordTrace_append hprefix tailTrace_76296
  have hstable : (prefixWord ++ tailWord_76296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76296).length < 2 ^ (prefixWord ++ tailWord_76296).sum := by decide
  have hdescent : baseEnd_76296 < baseStart_76296 := by decide
  rcases family_descends (prefixWord ++ tailWord_76296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76316 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_76316 : Nat := 118140960795 + 76316 * 2 ^ 59
def prefixEnd_76316 : Nat := 4983230072969 + 3 ^ 40 * 76316 * 2
def baseEnd_76316 : Nat := 39186789628628646999035

theorem tailTrace_76316 : CollatzResearch.WordTrace tailWord_76316 prefixEnd_76316 39186789628628646999035 := by
  unfold tailWord_76316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391736595763820290120401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1855648794351760386827201 1391736595763820290120401)
  ·
    refine ⟨1043802446822865217590301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1391736595763820290120401 1043802446822865217590301)
    ·
      refine ⟨391425917558574456596363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1043802446822865217590301 391425917558574456596363)
      ·
        refine ⟨587138876337861684894545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391425917558574456596363 587138876337861684894545)
        ·
          refine ⟨440354157253396263670909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587138876337861684894545 440354157253396263670909)
          ·
            refine ⟨165132808970023598876591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440354157253396263670909 165132808970023598876591)
            ·
              refine ⟨247699213455035398314887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165132808970023598876591 247699213455035398314887)
              ·
                refine ⟨371548820182553097472331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247699213455035398314887 371548820182553097472331)
                ·
                  refine ⟨557323230273829646208497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371548820182553097472331 557323230273829646208497)
                  ·
                    refine ⟨417992422705372234656373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 557323230273829646208497 417992422705372234656373)
                    ·
                      refine ⟨39186789628628646999035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 417992422705372234656373 39186789628628646999035)
                      ·
                        rfl

theorem cell23_76316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_76316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76316 prefixEnd_76316 := by exact prefixLift 76316
  have htrace : WordTrace (prefixWord ++ tailWord_76316) baseStart_76316 baseEnd_76316 := by
    simpa [prefixWord, tailWord_76316, baseEnd_76316] using wordTrace_append hprefix tailTrace_76316
  have hstable : (prefixWord ++ tailWord_76316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76316).length < 2 ^ (prefixWord ++ tailWord_76316).sum := by decide
  have hdescent : baseEnd_76316 < baseStart_76316 := by decide
  rcases family_descends (prefixWord ++ tailWord_76316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76336 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 3, 4]
def baseStart_76336 : Nat := 118140960795 + 76336 * 2 ^ 59
def prefixEnd_76336 : Nat := 4983230072969 + 3 ^ 40 * 76336 * 2
def baseEnd_76336 : Nat := 13065686413906189582981

theorem tailTrace_76336 : CollatzResearch.WordTrace tailWord_76336 prefixEnd_76336 13065686413906189582981 := by
  unfold tailWord_76336
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392101325727591997984431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1856135100970122663979241 1392101325727591997984431)
  ·
    refine ⟨2088151988591387996976647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1392101325727591997984431 2088151988591387996976647)
    ·
      refine ⟨3132227982887081995464971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2088151988591387996976647 3132227982887081995464971)
      ·
        refine ⟨4698341974330622993197457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132227982887081995464971 4698341974330622993197457)
        ·
          refine ⟨3523756480747967244898093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4698341974330622993197457 3523756480747967244898093)
          ·
            refine ⟨1321408680280487716836785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3523756480747967244898093 1321408680280487716836785)
            ·
              refine ⟨991056510210365787627589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321408680280487716836785 991056510210365787627589)
              ·
                refine ⟨185823095664443585180173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 991056510210365787627589 185823095664443585180173)
                ·
                  refine ⟨69683660874166344442565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185823095664443585180173 69683660874166344442565)
                  ·
                    refine ⟨13065686413906189582981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69683660874166344442565 13065686413906189582981)
                    ·
                      rfl

theorem cell23_76336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_76336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76336 prefixEnd_76336 := by exact prefixLift 76336
  have htrace : WordTrace (prefixWord ++ tailWord_76336) baseStart_76336 baseEnd_76336 := by
    simpa [prefixWord, tailWord_76336, baseEnd_76336] using wordTrace_append hprefix tailTrace_76336
  have hstable : (prefixWord ++ tailWord_76336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76336).length < 2 ^ (prefixWord ++ tailWord_76336).sum := by decide
  have hdescent : baseEnd_76336 < baseStart_76336 := by decide
  rcases family_descends (prefixWord ++ tailWord_76336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76366 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_76366 : Nat := 118140960795 + 76366 * 2 ^ 59
def prefixEnd_76366 : Nat := 4983230072969 + 3 ^ 40 * 76366 * 2
def baseEnd_76366 : Nat := 4356940406817050152645

theorem tailTrace_76366 : CollatzResearch.WordTrace tailWord_76366 prefixEnd_76366 4356940406817050152645 := by
  unfold tailWord_76366
  simp only [CollatzResearch.WordTrace]
  refine ⟨348162105168312389945119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1856864560897666079707301 348162105168312389945119)
  ·
    refine ⟨522243157752468584917679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 348162105168312389945119 522243157752468584917679)
    ·
      refine ⟨783364736628702877376519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522243157752468584917679 783364736628702877376519)
      ·
        refine ⟨1175047104943054316064779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783364736628702877376519 1175047104943054316064779)
        ·
          refine ⟨1762570657414581474097169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175047104943054316064779 1762570657414581474097169)
          ·
            refine ⟨1321927993060936105572877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762570657414581474097169 1321927993060936105572877)
            ·
              refine ⟨495722997397851039589829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1321927993060936105572877 495722997397851039589829)
              ·
                refine ⟨92948062012097069923093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 495722997397851039589829 92948062012097069923093)
                ·
                  refine ⟨4356940406817050152645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92948062012097069923093 4356940406817050152645)
                  ·
                    rfl

theorem cell23_76366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_76366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76366 prefixEnd_76366 := by exact prefixLift 76366
  have htrace : WordTrace (prefixWord ++ tailWord_76366) baseStart_76366 baseEnd_76366 := by
    simpa [prefixWord, tailWord_76366, baseEnd_76366] using wordTrace_append hprefix tailTrace_76366
  have hstable : (prefixWord ++ tailWord_76366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76366).length < 2 ^ (prefixWord ++ tailWord_76366).sum := by decide
  have hdescent : baseEnd_76366 < baseStart_76366 := by decide
  rcases family_descends (prefixWord ++ tailWord_76366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76370 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_76370 : Nat := 118140960795 + 76370 * 2 ^ 59
def prefixEnd_76370 : Nat := 4983230072969 + 3 ^ 40 * 76370 * 2
def baseEnd_76370 : Nat := 13071505861323811907929

theorem tailTrace_76370 : CollatzResearch.WordTrace tailWord_76370 prefixEnd_76370 13071505861323811907929 := by
  unfold tailWord_76370
  simp only [CollatzResearch.WordTrace]
  refine ⟨696360683333001950676641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1856961822221338535137709 696360683333001950676641)
  ·
    refine ⟨522270512499751463007481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 696360683333001950676641 522270512499751463007481)
    ·
      refine ⟨391702884374813597255611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 522270512499751463007481 391702884374813597255611)
      ·
        refine ⟨587554326562220395883417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391702884374813597255611 587554326562220395883417)
        ·
          refine ⟨440665744921665296912563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587554326562220395883417 440665744921665296912563)
          ·
            refine ⟨660998617382497945368845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440665744921665296912563 660998617382497945368845)
            ·
              refine ⟨247874481518436729513317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660998617382497945368845 247874481518436729513317)
              ·
                refine ⟨46476465284706886783747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247874481518436729513317 46476465284706886783747)
                ·
                  refine ⟨69714697927060330175621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46476465284706886783747 69714697927060330175621)
                  ·
                    refine ⟨13071505861323811907929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69714697927060330175621 13071505861323811907929)
                    ·
                      rfl

theorem cell23_76370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_76370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76370 prefixEnd_76370 := by exact prefixLift 76370
  have htrace : WordTrace (prefixWord ++ tailWord_76370) baseStart_76370 baseEnd_76370 := by
    simpa [prefixWord, tailWord_76370, baseEnd_76370] using wordTrace_append hprefix tailTrace_76370
  have hstable : (prefixWord ++ tailWord_76370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76370).length < 2 ^ (prefixWord ++ tailWord_76370).sum := by decide
  have hdescent : baseEnd_76370 < baseStart_76370 := by decide
  rcases family_descends (prefixWord ++ tailWord_76370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76396 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_76396 : Nat := 118140960795 + 76396 * 2 ^ 59
def prefixEnd_76396 : Nat := 4983230072969 + 3 ^ 40 * 76396 * 2
def baseEnd_76396 : Nat := 13075956026996111332889

theorem tailTrace_76396 : CollatzResearch.WordTrace tailWord_76396 prefixEnd_76396 13075956026996111332889 := by
  unfold tailWord_76396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393195515618907121576521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1857594020825209495435361 1393195515618907121576521)
  ·
    refine ⟨1044896636714180341182391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1393195515618907121576521 1044896636714180341182391)
    ·
      refine ⟨1567344955071270511773587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044896636714180341182391 1567344955071270511773587)
      ·
        refine ⟨2351017432606905767660381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567344955071270511773587 2351017432606905767660381)
        ·
          refine ⟨881631537227589662872643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2351017432606905767660381 881631537227589662872643)
          ·
            refine ⟨1322447305841384494308965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881631537227589662872643 1322447305841384494308965)
            ·
              refine ⟨247958869845259592682931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1322447305841384494308965 247958869845259592682931)
              ·
                refine ⟨371938304767889389024397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247958869845259592682931 371938304767889389024397)
                ·
                  refine ⟨139476864287958520884149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371938304767889389024397 139476864287958520884149)
                  ·
                    refine ⟨13075956026996111332889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139476864287958520884149 13075956026996111332889)
                    ·
                      rfl

theorem cell23_76396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_76396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76396 prefixEnd_76396 := by exact prefixLift 76396
  have htrace : WordTrace (prefixWord ++ tailWord_76396) baseStart_76396 baseEnd_76396 := by
    simpa [prefixWord, tailWord_76396, baseEnd_76396] using wordTrace_append hprefix tailTrace_76396
  have hstable : (prefixWord ++ tailWord_76396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76396).length < 2 ^ (prefixWord ++ tailWord_76396).sum := by decide
  have hdescent : baseEnd_76396 < baseStart_76396 := by decide
  rcases family_descends (prefixWord ++ tailWord_76396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76403 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 2, 3, 2]
def baseStart_76403 : Nat := 118140960795 + 76403 * 2 ^ 59
def prefixEnd_76403 : Nat := 4983230072969 + 3 ^ 40 * 76403 * 2
def baseEnd_76403 : Nat := 39231462445569806611135

theorem tailTrace_76403 : CollatzResearch.WordTrace tailWord_76403 prefixEnd_76403 39231462445569806611135 := by
  unfold tailWord_76403
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786646342212454438657863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1857764228141636292438575 2786646342212454438657863)
  ·
    refine ⟨4179969513318681657986795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2786646342212454438657863 4179969513318681657986795)
    ·
      refine ⟨6269954269978022486980193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4179969513318681657986795 6269954269978022486980193)
      ·
        refine ⟨4702465702483516865235145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269954269978022486980193 4702465702483516865235145)
        ·
          refine ⟨3526849276862637648926359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4702465702483516865235145 3526849276862637648926359)
          ·
            refine ⟨5290273915293956473389539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526849276862637648926359 5290273915293956473389539)
            ·
              refine ⟨7935410872940934710084309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290273915293956473389539 7935410872940934710084309)
              ·
                refine ⟨185986192334553157267601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7935410872940934710084309 185986192334553157267601)
                ·
                  refine ⟨139489644250914867950701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185986192334553157267601 139489644250914867950701)
                  ·
                    refine ⟨52308616594093075481513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139489644250914867950701 52308616594093075481513)
                    ·
                      refine ⟨39231462445569806611135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52308616594093075481513 39231462445569806611135)
                      ·
                        rfl

theorem cell23_76403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 3, 2].length) (baseStart_76403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76403 prefixEnd_76403 := by exact prefixLift 76403
  have htrace : WordTrace (prefixWord ++ tailWord_76403) baseStart_76403 baseEnd_76403 := by
    simpa [prefixWord, tailWord_76403, baseEnd_76403] using wordTrace_append hprefix tailTrace_76403
  have hstable : (prefixWord ++ tailWord_76403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76403).length < 2 ^ (prefixWord ++ tailWord_76403).sum := by decide
  have hdescent : baseEnd_76403 < baseStart_76403 := by decide
  rcases family_descends (prefixWord ++ tailWord_76403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76484 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_76484 : Nat := 118140960795 + 76484 * 2 ^ 59
def prefixEnd_76484 : Nat := 4983230072969 + 3 ^ 40 * 76484 * 2
def baseEnd_76484 : Nat := 39273054378583989698263

theorem tailTrace_76484 : CollatzResearch.WordTrace tailWord_76484 prefixEnd_76484 39273054378583989698263 := by
  unfold tailWord_76484
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394800327459502636178253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1859733769946003514904337 1394800327459502636178253)
  ·
    refine ⟨523050122797313488566845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1394800327459502636178253 523050122797313488566845)
    ·
      refine ⟨196143796048992558212567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 523050122797313488566845 196143796048992558212567)
      ·
        refine ⟨294215694073488837318851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196143796048992558212567 294215694073488837318851)
        ·
          refine ⟨441323541110233255978277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294215694073488837318851 441323541110233255978277)
          ·
            refine ⟨82748163958168735495927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 441323541110233255978277 82748163958168735495927)
            ·
              refine ⟨124122245937253103243891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82748163958168735495927 124122245937253103243891)
              ·
                refine ⟨186183368905879654865837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124122245937253103243891 186183368905879654865837)
                ·
                  refine ⟨69818763339704870574689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186183368905879654865837 69818763339704870574689)
                  ·
                    refine ⟨52364072504778652931017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69818763339704870574689 52364072504778652931017)
                    ·
                      refine ⟨39273054378583989698263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52364072504778652931017 39273054378583989698263)
                      ·
                        rfl

theorem cell23_76484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_76484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76484 prefixEnd_76484 := by exact prefixLift 76484
  have htrace : WordTrace (prefixWord ++ tailWord_76484) baseStart_76484 baseEnd_76484 := by
    simpa [prefixWord, tailWord_76484, baseEnd_76484] using wordTrace_append hprefix tailTrace_76484
  have hstable : (prefixWord ++ tailWord_76484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76484).length < 2 ^ (prefixWord ++ tailWord_76484).sum := by decide
  have hdescent : baseEnd_76484 < baseStart_76484 := by decide
  rcases family_descends (prefixWord ++ tailWord_76484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76593 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_76593 : Nat := 118140960795 + 76593 * 2 ^ 59
def prefixEnd_76593 : Nat := 4983230072969 + 3 ^ 40 * 76593 * 2
def baseEnd_76593 : Nat := 13109674589974687745087

theorem tailTrace_76593 : CollatzResearch.WordTrace tailWord_76593 prefixEnd_76593 13109674589974687745087 := by
  unfold tailWord_76593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793576211524116888074433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1862384141016077925382955 2793576211524116888074433)
  ·
    refine ⟨2095182158643087666055825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2793576211524116888074433 2095182158643087666055825)
    ·
      refine ⟨1571386618982315749541869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2095182158643087666055825 1571386618982315749541869)
      ·
        refine ⟨589269982118368406078201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1571386618982315749541869 589269982118368406078201)
        ·
          refine ⟨441952486588776304558651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589269982118368406078201 441952486588776304558651)
          ·
            refine ⟨662928729883164456837977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441952486588776304558651 662928729883164456837977)
            ·
              refine ⟨497196547412373342628483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662928729883164456837977 497196547412373342628483)
              ·
                refine ⟨745794821118560013942725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497196547412373342628483 745794821118560013942725)
                ·
                  refine ⟨139836528959730002614261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745794821118560013942725 139836528959730002614261)
                  ·
                    refine ⟨13109674589974687745087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139836528959730002614261 13109674589974687745087)
                    ·
                      rfl

theorem cell23_76593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_76593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76593 prefixEnd_76593 := by exact prefixLift 76593
  have htrace : WordTrace (prefixWord ++ tailWord_76593) baseStart_76593 baseEnd_76593 := by
    simpa [prefixWord, tailWord_76593, baseEnd_76593] using wordTrace_append hprefix tailTrace_76593
  have hstable : (prefixWord ++ tailWord_76593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76593).length < 2 ^ (prefixWord ++ tailWord_76593).sum := by decide
  have hdescent : baseEnd_76593 < baseStart_76593 := by decide
  rcases family_descends (prefixWord ++ tailWord_76593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76613 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_76613 : Nat := 118140960795 + 76613 * 2 ^ 59
def prefixEnd_76613 : Nat := 4983230072969 + 3 ^ 40 * 76613 * 2
def baseEnd_76613 : Nat := 39339293383013984985169

theorem tailTrace_76613 : CollatzResearch.WordTrace tailWord_76613 prefixEnd_76613 39339293383013984985169 := by
  unfold tailWord_76613
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794305671451660303802493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1862870447634440202534995 2794305671451660303802493)
  ·
    refine ⟨1047864626794372613925935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2794305671451660303802493 1047864626794372613925935)
    ·
      refine ⟨1571796940191558920888903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047864626794372613925935 1571796940191558920888903)
      ·
        refine ⟨2357695410287338381333355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571796940191558920888903 2357695410287338381333355)
        ·
          refine ⟨3536543115431007572000033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357695410287338381333355 3536543115431007572000033)
          ·
            refine ⟨2652407336573255679000025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3536543115431007572000033 2652407336573255679000025)
            ·
              refine ⟨1989305502429941759250019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652407336573255679000025 1989305502429941759250019)
              ·
                refine ⟨2983958253644912638875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989305502429941759250019 2983958253644912638875029)
                ·
                  refine ⟨139873043139605279947267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2983958253644912638875029 139873043139605279947267)
                  ·
                    refine ⟨209809564709407919920901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139873043139605279947267 209809564709407919920901)
                    ·
                      refine ⟨39339293383013984985169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 209809564709407919920901 39339293383013984985169)
                      ·
                        rfl

theorem cell23_76613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_76613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76613 prefixEnd_76613 := by exact prefixLift 76613
  have htrace : WordTrace (prefixWord ++ tailWord_76613) baseStart_76613 baseEnd_76613 := by
    simpa [prefixWord, tailWord_76613, baseEnd_76613] using wordTrace_append hprefix tailTrace_76613
  have hstable : (prefixWord ++ tailWord_76613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76613).length < 2 ^ (prefixWord ++ tailWord_76613).sum := by decide
  have hdescent : baseEnd_76613 < baseStart_76613 := by decide
  rcases family_descends (prefixWord ++ tailWord_76613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76657 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 3, 4]
def baseStart_76657 : Nat := 118140960795 + 76657 * 2 ^ 59
def prefixEnd_76657 : Nat := 4983230072969 + 3 ^ 40 * 76657 * 2
def baseEnd_76657 : Nat := 13120628843937270944989

theorem tailTrace_76657 : CollatzResearch.WordTrace tailWord_76657 prefixEnd_76657 13120628843937270944989 := by
  unfold tailWord_76657
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795910483292255818404225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1863940322194837212269483 2795910483292255818404225)
  ·
    refine ⟨2096932862469191863803169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2795910483292255818404225 2096932862469191863803169)
    ·
      refine ⟨1572699646851893897852377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2096932862469191863803169 1572699646851893897852377)
      ·
        refine ⟨1179524735138920423389283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1572699646851893897852377 1179524735138920423389283)
        ·
          refine ⟨1769287102708380635083925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179524735138920423389283 1769287102708380635083925)
          ·
            refine ⟨82935332939455342269559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1769287102708380635083925 82935332939455342269559)
            ·
              refine ⟨124402999409183013404339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82935332939455342269559 124402999409183013404339)
              ·
                refine ⟨186604499113774520106509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124402999409183013404339 186604499113774520106509)
                ·
                  refine ⟨69976687167665445039941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186604499113774520106509 69976687167665445039941)
                  ·
                    refine ⟨13120628843937270944989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69976687167665445039941 13120628843937270944989)
                    ·
                      rfl

theorem cell23_76657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_76657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76657 prefixEnd_76657 := by exact prefixLift 76657
  have htrace : WordTrace (prefixWord ++ tailWord_76657) baseStart_76657 baseEnd_76657 := by
    simpa [prefixWord, tailWord_76657, baseEnd_76657] using wordTrace_append hprefix tailTrace_76657
  have hstable : (prefixWord ++ tailWord_76657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76657).length < 2 ^ (prefixWord ++ tailWord_76657).sum := by decide
  have hdescent : baseEnd_76657 < baseStart_76657 := by decide
  rcases family_descends (prefixWord ++ tailWord_76657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76707 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 2, 3, 2]
def baseStart_76707 : Nat := 118140960795 + 76707 * 2 ^ 59
def prefixEnd_76707 : Nat := 4983230072969 + 3 ^ 40 * 76707 * 2
def baseEnd_76707 : Nat := 39387560564536617209737

theorem tailTrace_76707 : CollatzResearch.WordTrace tailWord_76707 prefixEnd_76707 39387560564536617209737 := by
  unfold tailWord_76707
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797734133111114357724375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1865156088740742905149583 2797734133111114357724375)
  ·
    refine ⟨4196601199666671536586563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2797734133111114357724375 4196601199666671536586563)
    ·
      refine ⟨6294901799500007304879845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4196601199666671536586563 6294901799500007304879845)
      ·
        refine ⟨1180294087406251369664971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6294901799500007304879845 1180294087406251369664971)
        ·
          refine ⟨1770441131109377054497457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180294087406251369664971 1770441131109377054497457)
          ·
            refine ⟨1327830848332032790873093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1770441131109377054497457 1327830848332032790873093)
            ·
              refine ⟨248968284062256148288705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1327830848332032790873093 248968284062256148288705)
              ·
                refine ⟨186726213046692111216529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248968284062256148288705 186726213046692111216529)
                ·
                  refine ⟨140044659785019083412397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186726213046692111216529 140044659785019083412397)
                  ·
                    refine ⟨52516747419382156279649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140044659785019083412397 52516747419382156279649)
                    ·
                      refine ⟨39387560564536617209737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52516747419382156279649 39387560564536617209737)
                      ·
                        rfl

theorem cell23_76707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_76707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76707 prefixEnd_76707 := by exact prefixLift 76707
  have htrace : WordTrace (prefixWord ++ tailWord_76707) baseStart_76707 baseEnd_76707 := by
    simpa [prefixWord, tailWord_76707, baseEnd_76707] using wordTrace_append hprefix tailTrace_76707
  have hstable : (prefixWord ++ tailWord_76707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76707).length < 2 ^ (prefixWord ++ tailWord_76707).sum := by decide
  have hdescent : baseEnd_76707 < baseStart_76707 := by decide
  rcases family_descends (prefixWord ++ tailWord_76707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76713 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_76713 : Nat := 118140960795 + 76713 * 2 ^ 59
def prefixEnd_76713 : Nat := 4983230072969 + 3 ^ 40 * 76713 * 2
def baseEnd_76713 : Nat := 13130213816154531244903

theorem tailTrace_76713 : CollatzResearch.WordTrace tailWord_76713 prefixEnd_76713 13130213816154531244903 := by
  unfold tailWord_76713
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797952971089377382442793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1865301980726251588295195 2797952971089377382442793)
  ·
    refine ⟨2098464728317033036832095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2797952971089377382442793 2098464728317033036832095)
    ·
      refine ⟨3147697092475549555248143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2098464728317033036832095 3147697092475549555248143)
      ·
        refine ⟨4721545638713324332872215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147697092475549555248143 4721545638713324332872215)
        ·
          refine ⟨7082318458069986499308323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721545638713324332872215 7082318458069986499308323)
          ·
            refine ⟨10623477687104979748962485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082318458069986499308323 10623477687104979748962485)
            ·
              refine ⟨995951033166091851465233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10623477687104979748962485 995951033166091851465233)
              ·
                refine ⟨746963274874568888598925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995951033166091851465233 746963274874568888598925)
                ·
                  refine ⟨280111228077963333224597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746963274874568888598925 280111228077963333224597)
                  ·
                    refine ⟨13130213816154531244903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 280111228077963333224597 13130213816154531244903)
                    ·
                      rfl

theorem cell23_76713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_76713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76713 prefixEnd_76713 := by exact prefixLift 76713
  have htrace : WordTrace (prefixWord ++ tailWord_76713) baseStart_76713 baseEnd_76713 := by
    simpa [prefixWord, tailWord_76713, baseEnd_76713] using wordTrace_append hprefix tailTrace_76713
  have hstable : (prefixWord ++ tailWord_76713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76713).length < 2 ^ (prefixWord ++ tailWord_76713).sum := by decide
  have hdescent : baseEnd_76713 < baseStart_76713 := by decide
  rcases family_descends (prefixWord ++ tailWord_76713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76730 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_76730 : Nat := 118140960795 + 76730 * 2 ^ 59
def prefixEnd_76730 : Nat := 4983230072969 + 3 ^ 40 * 76730 * 2
def baseEnd_76730 : Nat := 13133123539863342407377

theorem tailTrace_76730 : CollatzResearch.WordTrace tailWord_76730 prefixEnd_76730 13133123539863342407377 := by
  unfold tailWord_76730
  simp only [CollatzResearch.WordTrace]
  refine ⟨699643253006947321452911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1865715341351859523874429 699643253006947321452911)
  ·
    refine ⟨1049464879510420982179367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699643253006947321452911 1049464879510420982179367)
    ·
      refine ⟨1574197319265631473269051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049464879510420982179367 1574197319265631473269051)
      ·
        refine ⟨2361295978898447209903577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574197319265631473269051 2361295978898447209903577)
        ·
          refine ⟨1770971984173835407427683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2361295978898447209903577 1770971984173835407427683)
          ·
            refine ⟨2656457976260753111141525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770971984173835407427683 2656457976260753111141525)
            ·
              refine ⟨124521467637222802084759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2656457976260753111141525 124521467637222802084759)
              ·
                refine ⟨186782201455834203127139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124521467637222802084759 186782201455834203127139)
                ·
                  refine ⟨280173302183751304690709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186782201455834203127139 280173302183751304690709)
                  ·
                    refine ⟨13133123539863342407377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 280173302183751304690709 13133123539863342407377)
                    ·
                      rfl

theorem cell23_76730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_76730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76730 prefixEnd_76730 := by exact prefixLift 76730
  have htrace : WordTrace (prefixWord ++ tailWord_76730) baseStart_76730 baseEnd_76730 := by
    simpa [prefixWord, tailWord_76730, baseEnd_76730] using wordTrace_append hprefix tailTrace_76730
  have hstable : (prefixWord ++ tailWord_76730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76730).length < 2 ^ (prefixWord ++ tailWord_76730).sum := by decide
  have hdescent : baseEnd_76730 < baseStart_76730 := by decide
  rcases family_descends (prefixWord ++ tailWord_76730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76742 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_76742 : Nat := 118140960795 + 76742 * 2 ^ 59
def prefixEnd_76742 : Nat := 4983230072969 + 3 ^ 40 * 76742 * 2
def baseEnd_76742 : Nat := 13135177462481326757359

theorem tailTrace_76742 : CollatzResearch.WordTrace tailWord_76742 prefixEnd_76742 13135177462481326757359 := by
  unfold tailWord_76742
  simp only [CollatzResearch.WordTrace]
  refine ⟨87469083999509854226515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1866007125322876890165653 87469083999509854226515)
  ·
    refine ⟨131203625999264781339773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87469083999509854226515 131203625999264781339773)
    ·
      refine ⟨49201359749724293002415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131203625999264781339773 49201359749724293002415)
      ·
        refine ⟨73802039624586439503623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49201359749724293002415 73802039624586439503623)
        ·
          refine ⟨110703059436879659255435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73802039624586439503623 110703059436879659255435)
          ·
            refine ⟨166054589155319488883153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110703059436879659255435 166054589155319488883153)
            ·
              refine ⟨124540941866489616662365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166054589155319488883153 124540941866489616662365)
              ·
                refine ⟨46702853199933606248387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124540941866489616662365 46702853199933606248387)
                ·
                  refine ⟨70054279799900409372581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46702853199933606248387 70054279799900409372581)
                  ·
                    refine ⟨13135177462481326757359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70054279799900409372581 13135177462481326757359)
                    ·
                      rfl

theorem cell23_76742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_76742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76742 prefixEnd_76742 := by exact prefixLift 76742
  have htrace : WordTrace (prefixWord ++ tailWord_76742) baseStart_76742 baseEnd_76742 := by
    simpa [prefixWord, tailWord_76742, baseEnd_76742] using wordTrace_append hprefix tailTrace_76742
  have hstable : (prefixWord ++ tailWord_76742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76742).length < 2 ^ (prefixWord ++ tailWord_76742).sum := by decide
  have hdescent : baseEnd_76742 < baseStart_76742 := by decide
  rcases family_descends (prefixWord ++ tailWord_76742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76743 : List Nat := [1, 1, 4, 1, 1, 2, 2, 11]
def baseStart_76743 : Nat := 118140960795 + 76743 * 2 ^ 59
def prefixEnd_76743 : Nat := 4983230072969 + 3 ^ 40 * 76743 * 2
def baseEnd_76743 : Nat := 1459483180299943568873

theorem tailTrace_76743 : CollatzResearch.WordTrace tailWord_76743 prefixEnd_76743 1459483180299943568873 := by
  unfold tailWord_76743
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799047160980692506034883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1866031440653795004023255 2799047160980692506034883)
  ·
    refine ⟨4198570741471038759052325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799047160980692506034883 4198570741471038759052325)
    ·
      refine ⟨787232014025819767322311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4198570741471038759052325 787232014025819767322311)
      ·
        refine ⟨1180848021038729650983467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787232014025819767322311 1180848021038729650983467)
        ·
          refine ⟨1771272031558094476475201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180848021038729650983467 1771272031558094476475201)
          ·
            refine ⟨1328454023668570857356401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771272031558094476475201 1328454023668570857356401)
            ·
              refine ⟨996340517751428143017301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328454023668570857356401 996340517751428143017301)
              ·
                refine ⟨1459483180299943568873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 996340517751428143017301 1459483180299943568873)
                ·
                  rfl

theorem cell23_76743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 11].length) (baseStart_76743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76743 prefixEnd_76743 := by exact prefixLift 76743
  have htrace : WordTrace (prefixWord ++ tailWord_76743) baseStart_76743 baseEnd_76743 := by
    simpa [prefixWord, tailWord_76743, baseEnd_76743] using wordTrace_append hprefix tailTrace_76743
  have hstable : (prefixWord ++ tailWord_76743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76743).length < 2 ^ (prefixWord ++ tailWord_76743).sum := by decide
  have hdescent : baseEnd_76743 < baseStart_76743 := by decide
  rcases family_descends (prefixWord ++ tailWord_76743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76754 : List Nat := [3, 2, 2, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_76754 : Nat := 118140960795 + 76754 * 2 ^ 59
def prefixEnd_76754 : Nat := 4983230072969 + 3 ^ 40 * 76754 * 2
def baseEnd_76754 : Nat := 39411694155297933322021

theorem tailTrace_76754 : CollatzResearch.WordTrace tailWord_76754 prefixEnd_76754 39411694155297933322021 := by
  unfold tailWord_76754
  simp only [CollatzResearch.WordTrace]
  refine ⟨699862090985210346171329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1866298909293894256456877 699862090985210346171329)
  ·
    refine ⟨524896568238907759628497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 699862090985210346171329 524896568238907759628497)
    ·
      refine ⟨393672426179180819721373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524896568238907759628497 393672426179180819721373)
      ·
        refine ⟨147627159817192807395515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393672426179180819721373 147627159817192807395515)
        ·
          refine ⟨221440739725789211093273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147627159817192807395515 221440739725789211093273)
          ·
            refine ⟨166080554794341908319955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221440739725789211093273 166080554794341908319955)
            ·
              refine ⟨249120832191512862479933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166080554794341908319955 249120832191512862479933)
              ·
                refine ⟨93420312071817323429975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249120832191512862479933 93420312071817323429975)
                ·
                  refine ⟨140130468107725985144963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93420312071817323429975 140130468107725985144963)
                  ·
                    refine ⟨210195702161588977717445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140130468107725985144963 210195702161588977717445)
                    ·
                      refine ⟨39411694155297933322021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 210195702161588977717445 39411694155297933322021)
                      ·
                        rfl

theorem cell23_76754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_76754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76754 prefixEnd_76754 := by exact prefixLift 76754
  have htrace : WordTrace (prefixWord ++ tailWord_76754) baseStart_76754 baseEnd_76754 := by
    simpa [prefixWord, tailWord_76754, baseEnd_76754] using wordTrace_append hprefix tailTrace_76754
  have hstable : (prefixWord ++ tailWord_76754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76754).length < 2 ^ (prefixWord ++ tailWord_76754).sum := by decide
  have hdescent : baseEnd_76754 < baseStart_76754 := by decide
  rcases family_descends (prefixWord ++ tailWord_76754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76771 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 1, 2, 2]
def baseStart_76771 : Nat := 118140960795 + 76771 * 2 ^ 59
def prefixEnd_76771 : Nat := 4983230072969 + 3 ^ 40 * 76771 * 2
def baseEnd_76771 : Nat := 39420423326424366809443

theorem tailTrace_76771 : CollatzResearch.WordTrace tailWord_76771 prefixEnd_76771 39420423326424366809443 := by
  unfold tailWord_76771
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800068404879253288054167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1866712269919502192036111 2800068404879253288054167)
  ·
    refine ⟨4200102607318879932081251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800068404879253288054167 4200102607318879932081251)
    ·
      refine ⟨6300153910978319898121877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4200102607318879932081251 6300153910978319898121877)
      ·
        refine ⟨295319714577108745224463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6300153910978319898121877 295319714577108745224463)
        ·
          refine ⟨442979571865663117836695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295319714577108745224463 442979571865663117836695)
          ·
            refine ⟨664469357798494676755043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442979571865663117836695 664469357798494676755043)
            ·
              refine ⟨996704036697742015132565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664469357798494676755043 996704036697742015132565)
              ·
                refine ⟨46720501720206656959339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 996704036697742015132565 46720501720206656959339)
                ·
                  refine ⟨70080752580309985439009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46720501720206656959339 70080752580309985439009)
                  ·
                    refine ⟨52560564435232489079257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70080752580309985439009 52560564435232489079257)
                    ·
                      refine ⟨39420423326424366809443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 52560564435232489079257 39420423326424366809443)
                      ·
                        rfl

theorem cell23_76771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_76771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76771 prefixEnd_76771 := by exact prefixLift 76771
  have htrace : WordTrace (prefixWord ++ tailWord_76771) baseStart_76771 baseEnd_76771 := by
    simpa [prefixWord, tailWord_76771, baseEnd_76771] using wordTrace_append hprefix tailTrace_76771
  have hstable : (prefixWord ++ tailWord_76771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76771).length < 2 ^ (prefixWord ++ tailWord_76771).sum := by decide
  have hdescent : baseEnd_76771 < baseStart_76771 := by decide
  rcases family_descends (prefixWord ++ tailWord_76771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76850 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_76850 : Nat := 118140960795 + 76850 * 2 ^ 59
def prefixEnd_76850 : Nat := 4983230072969 + 3 ^ 40 * 76850 * 2
def baseEnd_76850 : Nat := 4384554255347728635731

theorem tailTrace_76850 : CollatzResearch.WordTrace tailWord_76850 prefixEnd_76850 4384554255347728635731 := by
  unfold tailWord_76850
  simp only [CollatzResearch.WordTrace]
  refine ⟨700737442898262445045001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1868633181062033186786669 700737442898262445045001)
  ·
    refine ⟨525553082173696833783751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 700737442898262445045001 525553082173696833783751)
    ·
      refine ⟨788329623260545250675627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525553082173696833783751 788329623260545250675627)
      ·
        refine ⟨1182494434890817876013441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788329623260545250675627 1182494434890817876013441)
        ·
          refine ⟨886870826168113407010081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182494434890817876013441 886870826168113407010081)
          ·
            refine ⟨665153119626085055257561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886870826168113407010081 665153119626085055257561)
            ·
              refine ⟨498864839719563791443171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665153119626085055257561 498864839719563791443171)
              ·
                refine ⟨748297259579345687164757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498864839719563791443171 748297259579345687164757)
                ·
                  refine ⟨4384554255347728635731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 748297259579345687164757 4384554255347728635731)
                  ·
                    rfl

theorem cell23_76850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_76850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76850 prefixEnd_76850 := by exact prefixLift 76850
  have htrace : WordTrace (prefixWord ++ tailWord_76850) baseStart_76850 baseEnd_76850 := by
    simpa [prefixWord, tailWord_76850, baseEnd_76850] using wordTrace_append hprefix tailTrace_76850
  have hstable : (prefixWord ++ tailWord_76850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76850).length < 2 ^ (prefixWord ++ tailWord_76850).sum := by decide
  have hdescent : baseEnd_76850 < baseStart_76850 := by decide
  rcases family_descends (prefixWord ++ tailWord_76850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76867 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 5]
def baseStart_76867 : Nat := 118140960795 + 76867 * 2 ^ 59
def prefixEnd_76867 : Nat := 4983230072969 + 3 ^ 40 * 76867 * 2
def baseEnd_76867 : Nat := 4385524163250665689889

theorem tailTrace_76867 : CollatzResearch.WordTrace tailWord_76867 prefixEnd_76867 4385524163250665689889 := by
  unfold tailWord_76867
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803569812531461683548855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1869046541687641122365903 2803569812531461683548855)
  ·
    refine ⟨4205354718797192525323283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2803569812531461683548855 4205354718797192525323283)
    ·
      refine ⟨6308032078195788787984925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205354718797192525323283 6308032078195788787984925)
      ·
        refine ⟨2365512029323420795494347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6308032078195788787984925 2365512029323420795494347)
        ·
          refine ⟨3548268043985131193241521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365512029323420795494347 3548268043985131193241521)
          ·
            refine ⟨2661201032988848394931141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3548268043985131193241521 2661201032988848394931141)
            ·
              refine ⟨498975193685409074049589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2661201032988848394931141 498975193685409074049589)
              ·
                refine ⟨46778924408007100692149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 498975193685409074049589 46778924408007100692149)
                ·
                  refine ⟨4385524163250665689889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46778924408007100692149 4385524163250665689889)
                  ·
                    rfl

theorem cell23_76867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 5].length) (baseStart_76867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76867 prefixEnd_76867 := by exact prefixLift 76867
  have htrace : WordTrace (prefixWord ++ tailWord_76867) baseStart_76867 baseEnd_76867 := by
    simpa [prefixWord, tailWord_76867, baseEnd_76867] using wordTrace_append hprefix tailTrace_76867
  have hstable : (prefixWord ++ tailWord_76867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76867).length < 2 ^ (prefixWord ++ tailWord_76867).sum := by decide
  have hdescent : baseEnd_76867 < baseStart_76867 := by decide
  rcases family_descends (prefixWord ++ tailWord_76867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76890 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_76890 : Nat := 118140960795 + 76890 * 2 ^ 59
def prefixEnd_76890 : Nat := 4983230072969 + 3 ^ 40 * 76890 * 2
def baseEnd_76890 : Nat := 39481527524309401221395

theorem tailTrace_76890 : CollatzResearch.WordTrace tailWord_76890 prefixEnd_76890 39481527524309401221395 := by
  unfold tailWord_76890
  simp only [CollatzResearch.WordTrace]
  refine ⟨701102172862034152909031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1869605794298757741090749 701102172862034152909031)
  ·
    refine ⟨1051653259293051229363547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701102172862034152909031 1051653259293051229363547)
    ·
      refine ⟨1577479888939576844045321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051653259293051229363547 1577479888939576844045321)
      ·
        refine ⟨1183109916704682633033991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1577479888939576844045321 1183109916704682633033991)
        ·
          refine ⟨1774664875057023949550987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183109916704682633033991 1774664875057023949550987)
          ·
            refine ⟨2661997312585535924326481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774664875057023949550987 2661997312585535924326481)
            ·
              refine ⟨1996497984439151943244861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661997312585535924326481 1996497984439151943244861)
              ·
                refine ⟨748686744164681978716823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1996497984439151943244861 748686744164681978716823)
                ·
                  refine ⟨1123030116247022968075235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748686744164681978716823 1123030116247022968075235)
                  ·
                    refine ⟨1684545174370534452112853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1123030116247022968075235 1684545174370534452112853)
                    ·
                      refine ⟨39481527524309401221395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1684545174370534452112853 39481527524309401221395)
                      ·
                        rfl

theorem cell23_76890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_76890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76890 prefixEnd_76890 := by exact prefixLift 76890
  have htrace : WordTrace (prefixWord ++ tailWord_76890) baseStart_76890 baseEnd_76890 := by
    simpa [prefixWord, tailWord_76890, baseEnd_76890] using wordTrace_append hprefix tailTrace_76890
  have hstable : (prefixWord ++ tailWord_76890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76890).length < 2 ^ (prefixWord ++ tailWord_76890).sum := by decide
  have hdescent : baseEnd_76890 < baseStart_76890 := by decide
  rcases family_descends (prefixWord ++ tailWord_76890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76954 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_76954 : Nat := 118140960795 + 76954 * 2 ^ 59
def prefixEnd_76954 : Nat := 4983230072969 + 3 ^ 40 * 76954 * 2
def baseEnd_76954 : Nat := 39514390286197150821101

theorem tailTrace_76954 : CollatzResearch.WordTrace tailWord_76954 prefixEnd_76954 39514390286197150821101 := by
  unfold tailWord_76954
  simp only [CollatzResearch.WordTrace]
  refine ⟨701685740804068885491479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1871161975477517027977277 701685740804068885491479)
  ·
    refine ⟨1052528611206103328237219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701685740804068885491479 1052528611206103328237219)
    ·
      refine ⟨1578792916809154992355829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052528611206103328237219 1578792916809154992355829)
      ·
        refine ⟨148011835950858280533359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1578792916809154992355829 148011835950858280533359)
        ·
          refine ⟨222017753926287420800039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148011835950858280533359 222017753926287420800039)
          ·
            refine ⟨333026630889431131200059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222017753926287420800039 333026630889431131200059)
            ·
              refine ⟨499539946334146696800089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333026630889431131200059 499539946334146696800089)
              ·
                refine ⟨374654959750610022600067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499539946334146696800089 374654959750610022600067)
                ·
                  refine ⟨561982439625915033900101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374654959750610022600067 561982439625915033900101)
                  ·
                    refine ⟨105371707429859068856269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 561982439625915033900101 105371707429859068856269)
                    ·
                      refine ⟨39514390286197150821101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 105371707429859068856269 39514390286197150821101)
                      ·
                        rfl

theorem cell23_76954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_76954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76954 prefixEnd_76954 := by exact prefixLift 76954
  have htrace : WordTrace (prefixWord ++ tailWord_76954) baseStart_76954 baseEnd_76954 := by
    simpa [prefixWord, tailWord_76954, baseEnd_76954] using wordTrace_append hprefix tailTrace_76954
  have hstable : (prefixWord ++ tailWord_76954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76954).length < 2 ^ (prefixWord ++ tailWord_76954).sum := by decide
  have hdescent : baseEnd_76954 < baseStart_76954 := by decide
  rcases family_descends (prefixWord ++ tailWord_76954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76978 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_76978 : Nat := 118140960795 + 76978 * 2 ^ 59
def prefixEnd_76978 : Nat := 4983230072969 + 3 ^ 40 * 76978 * 2
def baseEnd_76978 : Nat := 13175571273968352306997

theorem tailTrace_76978 : CollatzResearch.WordTrace tailWord_76978 prefixEnd_76978 13175571273968352306997 := by
  unfold tailWord_76978
  simp only [CollatzResearch.WordTrace]
  refine ⟨701904578782331910209897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1871745543419551760559725 701904578782331910209897)
  ·
    refine ⟨526428434086748932657423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 701904578782331910209897 526428434086748932657423)
    ·
      refine ⟨789642651130123398986135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526428434086748932657423 789642651130123398986135)
      ·
        refine ⟨1184463976695185098479203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789642651130123398986135 1184463976695185098479203)
        ·
          refine ⟨1776695965042777647718805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184463976695185098479203 1776695965042777647718805)
          ·
            refine ⟨83282623361380202236819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1776695965042777647718805 83282623361380202236819)
            ·
              refine ⟨124923935042070303355229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83282623361380202236819 124923935042070303355229)
              ·
                refine ⟨46846475640776363758211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124923935042070303355229 46846475640776363758211)
                ·
                  refine ⟨70269713461164545637317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46846475640776363758211 70269713461164545637317)
                  ·
                    refine ⟨13175571273968352306997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70269713461164545637317 13175571273968352306997)
                    ·
                      rfl

theorem cell23_76978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_76978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76978 prefixEnd_76978 := by exact prefixLift 76978
  have htrace : WordTrace (prefixWord ++ tailWord_76978) baseStart_76978 baseEnd_76978 := by
    simpa [prefixWord, tailWord_76978, baseEnd_76978] using wordTrace_append hprefix tailTrace_76978
  have hstable : (prefixWord ++ tailWord_76978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76978).length < 2 ^ (prefixWord ++ tailWord_76978).sum := by decide
  have hdescent : baseEnd_76978 < baseStart_76978 := by decide
  rcases family_descends (prefixWord ++ tailWord_76978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77017 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_77017 : Nat := 118140960795 + 77017 * 2 ^ 59
def prefixEnd_77017 : Nat := 4983230072969 + 3 ^ 40 * 77017 * 2
def baseEnd_77017 : Nat := 13182246522476801444437

theorem tailTrace_77017 : CollatzResearch.WordTrace tailWord_77017 prefixEnd_77017 13182246522476801444437 := by
  unfold tailWord_77017
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809040761988037301509305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1872693841325358201006203 2809040761988037301509305)
  ·
    refine ⟨2106780571491027976131979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2809040761988037301509305 2106780571491027976131979)
    ·
      refine ⟨3160170857236541964197969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2106780571491027976131979 3160170857236541964197969)
      ·
        refine ⟨2370128142927406473148477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3160170857236541964197969 2370128142927406473148477)
        ·
          refine ⟨888798053597777427430679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2370128142927406473148477 888798053597777427430679)
          ·
            refine ⟨1333197080396666141146019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888798053597777427430679 1333197080396666141146019)
            ·
              refine ⟨1999795620594999211719029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333197080396666141146019 1999795620594999211719029)
              ·
                refine ⟨187480839430781176098659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1999795620594999211719029 187480839430781176098659)
                ·
                  refine ⟨281221259146171764147989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187480839430781176098659 281221259146171764147989)
                  ·
                    refine ⟨13182246522476801444437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 281221259146171764147989 13182246522476801444437)
                    ·
                      rfl

theorem cell23_77017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_77017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77017 prefixEnd_77017 := by exact prefixLift 77017
  have htrace : WordTrace (prefixWord ++ tailWord_77017) baseStart_77017 baseEnd_77017 := by
    simpa [prefixWord, tailWord_77017, baseEnd_77017] using wordTrace_append hprefix tailTrace_77017
  have hstable : (prefixWord ++ tailWord_77017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77017).length < 2 ^ (prefixWord ++ tailWord_77017).sum := by decide
  have hdescent : baseEnd_77017 < baseStart_77017 := by decide
  rcases family_descends (prefixWord ++ tailWord_77017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77021 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_77021 : Nat := 118140960795 + 77021 * 2 ^ 59
def prefixEnd_77021 : Nat := 4983230072969 + 3 ^ 40 * 77021 * 2
def baseEnd_77021 : Nat := 13182931163349462894431

theorem tailTrace_77021 : CollatzResearch.WordTrace tailWord_77021 prefixEnd_77021 13182931163349462894431 := by
  unfold tailWord_77021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809186653973545984654917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1872791102649030656436611 2809186653973545984654917)
  ·
    refine ⟨526722497620039872122797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2809186653973545984654917 526722497620039872122797)
    ·
      refine ⟨197520936607514952046049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 526722497620039872122797 197520936607514952046049)
      ·
        refine ⟨148140702455636214034537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197520936607514952046049 148140702455636214034537)
        ·
          refine ⟨111105526841727160525903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148140702455636214034537 111105526841727160525903)
          ·
            refine ⟨166658290262590740788855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111105526841727160525903 166658290262590740788855)
            ·
              refine ⟨249987435393886111183283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166658290262590740788855 249987435393886111183283)
              ·
                refine ⟨374981153090829166774925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249987435393886111183283 374981153090829166774925)
                ·
                  refine ⟨140617932409060937540597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374981153090829166774925 140617932409060937540597)
                  ·
                    refine ⟨13182931163349462894431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 140617932409060937540597 13182931163349462894431)
                    ·
                      rfl

theorem cell23_77021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_77021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77021 prefixEnd_77021 := by exact prefixLift 77021
  have htrace : WordTrace (prefixWord ++ tailWord_77021) baseStart_77021 baseEnd_77021 := by
    simpa [prefixWord, tailWord_77021, baseEnd_77021] using wordTrace_append hprefix tailTrace_77021
  have hstable : (prefixWord ++ tailWord_77021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77021).length < 2 ^ (prefixWord ++ tailWord_77021).sum := by decide
  have hdescent : baseEnd_77021 < baseStart_77021 := by decide
  rcases family_descends (prefixWord ++ tailWord_77021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77024 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_77024 : Nat := 118140960795 + 77024 * 2 ^ 59
def prefixEnd_77024 : Nat := 4983230072969 + 3 ^ 40 * 77024 * 2
def baseEnd_77024 : Nat := 39550333932011876945779

theorem tailTrace_77024 : CollatzResearch.WordTrace tailWord_77024 prefixEnd_77024 39550333932011876945779 := by
  unfold tailWord_77024
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404648036481338748507063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1872864048641784998009417 1404648036481338748507063)
  ·
    refine ⟨2106972054722008122760595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404648036481338748507063 2106972054722008122760595)
    ·
      refine ⟨3160458082083012184140893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2106972054722008122760595 3160458082083012184140893)
      ·
        refine ⟨1185171780781129569052835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3160458082083012184140893 1185171780781129569052835)
        ·
          refine ⟨1777757671171694353579253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185171780781129569052835 1777757671171694353579253)
          ·
            refine ⟨166664781672346345648055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1777757671171694353579253 166664781672346345648055)
            ·
              refine ⟨249997172508519518472083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166664781672346345648055 249997172508519518472083)
              ·
                refine ⟨374995758762779277708125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249997172508519518472083 374995758762779277708125)
                ·
                  refine ⟨140623409536042229140547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374995758762779277708125 140623409536042229140547)
                  ·
                    refine ⟨210935114304063343710821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140623409536042229140547 210935114304063343710821)
                    ·
                      refine ⟨39550333932011876945779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 210935114304063343710821 39550333932011876945779)
                      ·
                        rfl

theorem cell23_77024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_77024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77024 prefixEnd_77024 := by exact prefixLift 77024
  have htrace : WordTrace (prefixWord ++ tailWord_77024) baseStart_77024 baseEnd_77024 := by
    simpa [prefixWord, tailWord_77024, baseEnd_77024] using wordTrace_append hprefix tailTrace_77024
  have hstable : (prefixWord ++ tailWord_77024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77024).length < 2 ^ (prefixWord ++ tailWord_77024).sum := by decide
  have hdescent : baseEnd_77024 < baseStart_77024 := by decide
  rcases family_descends (prefixWord ++ tailWord_77024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77034 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_77034 : Nat := 118140960795 + 77034 * 2 ^ 59
def prefixEnd_77034 : Nat := 4983230072969 + 3 ^ 40 * 77034 * 2
def baseEnd_77034 : Nat := 13185156246185612606911

theorem tailTrace_77034 : CollatzResearch.WordTrace tailWord_77034 prefixEnd_77034 13185156246185612606911 := by
  unfold tailWord_77034
  simp only [CollatzResearch.WordTrace]
  refine ⟨702415200731612301219539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1873107201950966136585437 702415200731612301219539)
  ·
    refine ⟨1053622801097418451829309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702415200731612301219539 1053622801097418451829309)
    ·
      refine ⟨395108550411531919435991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1053622801097418451829309 395108550411531919435991)
      ·
        refine ⟨592662825617297879153987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395108550411531919435991 592662825617297879153987)
        ·
          refine ⟨888994238425946818730981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592662825617297879153987 888994238425946818730981)
          ·
            refine ⟨166686419704865028512059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 888994238425946818730981 166686419704865028512059)
            ·
              refine ⟨250029629557297542768089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166686419704865028512059 250029629557297542768089)
              ·
                refine ⟨187522222167973157076067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250029629557297542768089 187522222167973157076067)
                ·
                  refine ⟨281283333251959735614101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187522222167973157076067 281283333251959735614101)
                  ·
                    refine ⟨13185156246185612606911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 281283333251959735614101 13185156246185612606911)
                    ·
                      rfl

theorem cell23_77034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_77034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77034 prefixEnd_77034 := by exact prefixLift 77034
  have htrace : WordTrace (prefixWord ++ tailWord_77034) baseStart_77034 baseEnd_77034 := by
    simpa [prefixWord, tailWord_77034, baseEnd_77034] using wordTrace_append hprefix tailTrace_77034
  have hstable : (prefixWord ++ tailWord_77034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77034).length < 2 ^ (prefixWord ++ tailWord_77034).sum := by decide
  have hdescent : baseEnd_77034 < baseStart_77034 := by decide
  rcases family_descends (prefixWord ++ tailWord_77034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77052 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_77052 : Nat := 118140960795 + 77052 * 2 ^ 59
def prefixEnd_77052 : Nat := 4983230072969 + 3 ^ 40 * 77052 * 2
def baseEnd_77052 : Nat := 39564711390337767395651

theorem tailTrace_77052 : CollatzResearch.WordTrace tailWord_77052 prefixEnd_77052 39564711390337767395651 := by
  unfold tailWord_77052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405158658430619139516705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1873544877907492186022273 1405158658430619139516705)
  ·
    refine ⟨1053868993822964354637529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1405158658430619139516705 1053868993822964354637529)
    ·
      refine ⟨790401745367223265978147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053868993822964354637529 790401745367223265978147)
      ·
        refine ⟨1185602618050834898967221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790401745367223265978147 1185602618050834898967221)
        ·
          refine ⟨111150245442265771778177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1185602618050834898967221 111150245442265771778177)
          ·
            refine ⟨83362684081699328833633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111150245442265771778177 83362684081699328833633)
            ·
              refine ⟨62522013061274496625225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83362684081699328833633 62522013061274496625225)
              ·
                refine ⟨46891509795955872468919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62522013061274496625225 46891509795955872468919)
                ·
                  refine ⟨70337264693933808703379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46891509795955872468919 70337264693933808703379)
                  ·
                    refine ⟨105505897040900713055069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70337264693933808703379 105505897040900713055069)
                    ·
                      refine ⟨39564711390337767395651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 105505897040900713055069 39564711390337767395651)
                      ·
                        rfl

theorem cell23_77052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_77052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77052 prefixEnd_77052 := by exact prefixLift 77052
  have htrace : WordTrace (prefixWord ++ tailWord_77052) baseStart_77052 baseEnd_77052 := by
    simpa [prefixWord, tailWord_77052, baseEnd_77052] using wordTrace_append hprefix tailTrace_77052
  have hstable : (prefixWord ++ tailWord_77052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77052).length < 2 ^ (prefixWord ++ tailWord_77052).sum := by decide
  have hdescent : baseEnd_77052 < baseStart_77052 := by decide
  rcases family_descends (prefixWord ++ tailWord_77052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77077 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_77077 : Nat := 118140960795 + 77077 * 2 ^ 59
def prefixEnd_77077 : Nat := 4983230072969 + 3 ^ 40 * 77077 * 2
def baseEnd_77077 : Nat := 13192516135566723194345

theorem tailTrace_77077 : CollatzResearch.WordTrace tailWord_77077 prefixEnd_77077 13192516135566723194345 := by
  unfold tailWord_77077
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811229141770667548693485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1874152761180445032462323 2811229141770667548693485)
  ·
    refine ⟨1054210928164000330760057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2811229141770667548693485 1054210928164000330760057)
    ·
      refine ⟨790658196123000248070043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1054210928164000330760057 790658196123000248070043)
      ·
        refine ⟨1185987294184500372105065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790658196123000248070043 1185987294184500372105065)
        ·
          refine ⟨889490470638375279078799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185987294184500372105065 889490470638375279078799)
          ·
            refine ⟨1334235705957562918618199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889490470638375279078799 1334235705957562918618199)
            ·
              refine ⟨2001353558936344377927299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334235705957562918618199 2001353558936344377927299)
              ·
                refine ⟨3002030338404516566890949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001353558936344377927299 3002030338404516566890949)
                ·
                  refine ⟨562880688450846856292053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3002030338404516566890949 562880688450846856292053)
                  ·
                    refine ⟨13192516135566723194345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 562880688450846856292053 13192516135566723194345)
                    ·
                      rfl

theorem cell23_77077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_77077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77077 prefixEnd_77077 := by exact prefixLift 77077
  have htrace : WordTrace (prefixWord ++ tailWord_77077) baseStart_77077 baseEnd_77077 := by
    simpa [prefixWord, tailWord_77077, baseEnd_77077] using wordTrace_append hprefix tailTrace_77077
  have hstable : (prefixWord ++ tailWord_77077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77077).length < 2 ^ (prefixWord ++ tailWord_77077).sum := by decide
  have hdescent : baseEnd_77077 < baseStart_77077 := by decide
  rcases family_descends (prefixWord ++ tailWord_77077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77108 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_77108 : Nat := 118140960795 + 77108 * 2 ^ 59
def prefixEnd_77108 : Nat := 4983230072969 + 3 ^ 40 * 77108 * 2
def baseEnd_77108 : Nat := 39593466306989548295393

theorem tailTrace_77108 : CollatzResearch.WordTrace tailWord_77108 prefixEnd_77108 39593466306989548295393 := by
  unfold tailWord_77108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406179902329179921535989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1874906536438906562047985 1406179902329179921535989)
  ·
    refine ⟨131829365843360617643999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1406179902329179921535989 131829365843360617643999)
    ·
      refine ⟨197744048765040926465999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131829365843360617643999 197744048765040926465999)
      ·
        refine ⟨296616073147561389698999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197744048765040926465999 296616073147561389698999)
        ·
          refine ⟨444924109721342084548499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296616073147561389698999 444924109721342084548499)
          ·
            refine ⟨667386164582013126822749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444924109721342084548499 667386164582013126822749)
            ·
              refine ⟨250269811718254922558531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 667386164582013126822749 250269811718254922558531)
              ·
                refine ⟨375404717577382383837797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250269811718254922558531 375404717577382383837797)
                ·
                  refine ⟨70388384545759196969587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375404717577382383837797 70388384545759196969587)
                  ·
                    refine ⟨105582576818638795454381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70388384545759196969587 105582576818638795454381)
                    ·
                      refine ⟨39593466306989548295393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 105582576818638795454381 39593466306989548295393)
                      ·
                        rfl

theorem cell23_77108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_77108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77108 prefixEnd_77108 := by exact prefixLift 77108
  have htrace : WordTrace (prefixWord ++ tailWord_77108) baseStart_77108 baseEnd_77108 := by
    simpa [prefixWord, tailWord_77108, baseEnd_77108] using wordTrace_append hprefix tailTrace_77108
  have hstable : (prefixWord ++ tailWord_77108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77108).length < 2 ^ (prefixWord ++ tailWord_77108).sum := by decide
  have hdescent : baseEnd_77108 < baseStart_77108 := by decide
  rcases family_descends (prefixWord ++ tailWord_77108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77134 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_77134 : Nat := 118140960795 + 77134 * 2 ^ 59
def prefixEnd_77134 : Nat := 4983230072969 + 3 ^ 40 * 77134 * 2
def baseEnd_77134 : Nat := 39606816804006446570273

theorem tailTrace_77134 : CollatzResearch.WordTrace tailWord_77134 prefixEnd_77134 39606816804006446570273 := by
  unfold tailWord_77134
  simp only [CollatzResearch.WordTrace]
  refine ⟨351663512820520785439807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1875538735042777522345637 351663512820520785439807)
  ·
    refine ⟨527495269230781178159711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351663512820520785439807 527495269230781178159711)
    ·
      refine ⟨791242903846171767239567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527495269230781178159711 791242903846171767239567)
      ·
        refine ⟨1186864355769257650859351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791242903846171767239567 1186864355769257650859351)
        ·
          refine ⟨1780296533653886476289027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186864355769257650859351 1780296533653886476289027)
          ·
            refine ⟨2670444800480829714433541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780296533653886476289027 2670444800480829714433541)
            ·
              refine ⟨500708400090155571456289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2670444800480829714433541 500708400090155571456289)
              ·
                refine ⟨375531300067616678592217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500708400090155571456289 375531300067616678592217)
                ·
                  refine ⟨281648475050712508944163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375531300067616678592217 281648475050712508944163)
                  ·
                    refine ⟨422472712576068763416245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 281648475050712508944163 422472712576068763416245)
                    ·
                      refine ⟨39606816804006446570273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 422472712576068763416245 39606816804006446570273)
                      ·
                        rfl

theorem cell23_77134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_77134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77134 prefixEnd_77134 := by exact prefixLift 77134
  have htrace : WordTrace (prefixWord ++ tailWord_77134) baseStart_77134 baseEnd_77134 := by
    simpa [prefixWord, tailWord_77134, baseEnd_77134] using wordTrace_append hprefix tailTrace_77134
  have hstable : (prefixWord ++ tailWord_77134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77134).length < 2 ^ (prefixWord ++ tailWord_77134).sum := by decide
  have hdescent : baseEnd_77134 < baseStart_77134 := by decide
  rcases family_descends (prefixWord ++ tailWord_77134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77234 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_77234 : Nat := 118140960795 + 77234 * 2 ^ 59
def prefixEnd_77234 : Nat := 4983230072969 + 3 ^ 40 * 77234 * 2
def baseEnd_77234 : Nat := 39658164869456055319813

theorem tailTrace_77234 : CollatzResearch.WordTrace tailWord_77234 prefixEnd_77234 39658164869456055319813 := by
  unfold tailWord_77234
  simp only [CollatzResearch.WordTrace]
  refine ⟨704238850550470840539689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1877970268134588908105837 704238850550470840539689)
  ·
    refine ⟨528179137912853130404767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 704238850550470840539689 528179137912853130404767)
    ·
      refine ⟨792268706869279695607151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528179137912853130404767 792268706869279695607151)
      ·
        refine ⟨1188403060303919543410727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792268706869279695607151 1188403060303919543410727)
        ·
          refine ⟨1782604590455879315116091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188403060303919543410727 1782604590455879315116091)
          ·
            refine ⟨2673906885683818972674137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782604590455879315116091 2673906885683818972674137)
            ·
              refine ⟨2005430164262864229505603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673906885683818972674137 2005430164262864229505603)
              ·
                refine ⟨3008145246394296344258405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005430164262864229505603 3008145246394296344258405)
                ·
                  refine ⟨564027233698930564548451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3008145246394296344258405 564027233698930564548451)
                  ·
                    refine ⟨846040850548395846822677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 564027233698930564548451 846040850548395846822677)
                    ·
                      refine ⟨39658164869456055319813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 846040850548395846822677 39658164869456055319813)
                      ·
                        rfl

theorem cell23_77234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_77234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77234 prefixEnd_77234 := by exact prefixLift 77234
  have htrace : WordTrace (prefixWord ++ tailWord_77234) baseStart_77234 baseEnd_77234 := by
    simpa [prefixWord, tailWord_77234, baseEnd_77234] using wordTrace_append hprefix tailTrace_77234
  have hstable : (prefixWord ++ tailWord_77234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77234).length < 2 ^ (prefixWord ++ tailWord_77234).sum := by decide
  have hdescent : baseEnd_77234 < baseStart_77234 := by decide
  rcases family_descends (prefixWord ++ tailWord_77234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77258 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_77258 : Nat := 118140960795 + 77258 * 2 ^ 59
def prefixEnd_77258 : Nat := 4983230072969 + 3 ^ 40 * 77258 * 2
def baseEnd_77258 : Nat := 39670488405163961419703

theorem tailTrace_77258 : CollatzResearch.WordTrace tailWord_77258 prefixEnd_77258 39670488405163961419703 := by
  unfold tailWord_77258
  simp only [CollatzResearch.WordTrace]
  refine ⟨704457688528733865258107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1878553836076623640688285 704457688528733865258107)
  ·
    refine ⟨1056686532793100797887161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 704457688528733865258107 1056686532793100797887161)
    ·
      refine ⟨792514899594825598415371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1056686532793100797887161 792514899594825598415371)
      ·
        refine ⟨1188772349392238397623057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792514899594825598415371 1188772349392238397623057)
        ·
          refine ⟨891579262044178798217293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188772349392238397623057 891579262044178798217293)
          ·
            refine ⟨334342223266567049331485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 891579262044178798217293 334342223266567049331485)
            ·
              refine ⟨125378333724962643499307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334342223266567049331485 125378333724962643499307)
              ·
                refine ⟨188067500587443965248961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125378333724962643499307 188067500587443965248961)
                ·
                  refine ⟨141050625440582973936721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188067500587443965248961 141050625440582973936721)
                  ·
                    refine ⟨105787969080437230452541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141050625440582973936721 105787969080437230452541)
                    ·
                      refine ⟨39670488405163961419703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 105787969080437230452541 39670488405163961419703)
                      ·
                        rfl

theorem cell23_77258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_77258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77258 prefixEnd_77258 := by exact prefixLift 77258
  have htrace : WordTrace (prefixWord ++ tailWord_77258) baseStart_77258 baseEnd_77258 := by
    simpa [prefixWord, tailWord_77258, baseEnd_77258] using wordTrace_append hprefix tailTrace_77258
  have hstable : (prefixWord ++ tailWord_77258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77258).length < 2 ^ (prefixWord ++ tailWord_77258).sum := by decide
  have hdescent : baseEnd_77258 < baseStart_77258 := by decide
  rcases family_descends (prefixWord ++ tailWord_77258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77321 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 6, 4]
def baseStart_77321 : Nat := 118140960795 + 77321 * 2 ^ 59
def prefixEnd_77321 : Nat := 4983230072969 + 3 ^ 40 * 77321 * 2
def baseEnd_77321 : Nat := 13234279228799071643971

theorem tailTrace_77321 : CollatzResearch.WordTrace tailWord_77321 prefixEnd_77321 13234279228799071643971 := by
  unfold tailWord_77321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820128552886697220575817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1880085701924464813717211 2820128552886697220575817)
  ·
    refine ⟨2115096414665022915431863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2820128552886697220575817 2115096414665022915431863)
    ·
      refine ⟨3172644621997534373147795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115096414665022915431863 3172644621997534373147795)
      ·
        refine ⟨4758966932996301559721693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172644621997534373147795 4758966932996301559721693)
        ·
          refine ⟨1784612599873613084895635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4758966932996301559721693 1784612599873613084895635)
          ·
            refine ⟨2676918899810419627343453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784612599873613084895635 2676918899810419627343453)
            ·
              refine ⟨1003844587428907360253795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2676918899810419627343453 1003844587428907360253795)
              ·
                refine ⟨1505766881143361040380693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003844587428907360253795 1505766881143361040380693)
                ·
                  refine ⟨70582822553595048767845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1505766881143361040380693 70582822553595048767845)
                  ·
                    refine ⟨13234279228799071643971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70582822553595048767845 13234279228799071643971)
                    ·
                      rfl

theorem cell23_77321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_77321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77321 prefixEnd_77321 := by exact prefixLift 77321
  have htrace : WordTrace (prefixWord ++ tailWord_77321) baseStart_77321 baseEnd_77321 := by
    simpa [prefixWord, tailWord_77321, baseEnd_77321] using wordTrace_append hprefix tailTrace_77321
  have hstable : (prefixWord ++ tailWord_77321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77321).length < 2 ^ (prefixWord ++ tailWord_77321).sum := by decide
  have hdescent : baseEnd_77321 < baseStart_77321 := by decide
  rcases family_descends (prefixWord ++ tailWord_77321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77322 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_77322 : Nat := 118140960795 + 77322 * 2 ^ 59
def prefixEnd_77322 : Nat := 4983230072969 + 3 ^ 40 * 77322 * 2
def baseEnd_77322 : Nat := 39703351167051711019409

theorem tailTrace_77322 : CollatzResearch.WordTrace tailWord_77322 prefixEnd_77322 39703351167051711019409 := by
  unfold tailWord_77322
  simp only [CollatzResearch.WordTrace]
  refine ⟨705041256470768597840555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1880110017255382927574813 705041256470768597840555)
  ·
    refine ⟨1057561884706152896760833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705041256470768597840555 1057561884706152896760833)
    ·
      refine ⟨793171413529614672570625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057561884706152896760833 793171413529614672570625)
      ·
        refine ⟨594878560147211004427969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793171413529614672570625 594878560147211004427969)
        ·
          refine ⟨446158920110408253320977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594878560147211004427969 446158920110408253320977)
          ·
            refine ⟨334619190082806189990733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446158920110408253320977 334619190082806189990733)
            ·
              refine ⟨125482196281052321246525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334619190082806189990733 125482196281052321246525)
              ·
                refine ⟨47055823605394620467447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125482196281052321246525 47055823605394620467447)
                ·
                  refine ⟨70583735408091930701171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47055823605394620467447 70583735408091930701171)
                  ·
                    refine ⟨105875603112137896051757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70583735408091930701171 105875603112137896051757)
                    ·
                      refine ⟨39703351167051711019409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 105875603112137896051757 39703351167051711019409)
                      ·
                        rfl

theorem cell23_77322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_77322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77322 prefixEnd_77322 := by exact prefixLift 77322
  have htrace : WordTrace (prefixWord ++ tailWord_77322) baseStart_77322 baseEnd_77322 := by
    simpa [prefixWord, tailWord_77322, baseEnd_77322] using wordTrace_append hprefix tailTrace_77322
  have hstable : (prefixWord ++ tailWord_77322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77322).length < 2 ^ (prefixWord ++ tailWord_77322).sum := by decide
  have hdescent : baseEnd_77322 < baseStart_77322 := by decide
  rcases family_descends (prefixWord ++ tailWord_77322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77331 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5]
def baseStart_77331 : Nat := 118140960795 + 77331 * 2 ^ 59
def prefixEnd_77331 : Nat := 4983230072969 + 3 ^ 40 * 77331 * 2
def baseEnd_77331 : Nat := 39707972492942175806867

theorem tailTrace_77331 : CollatzResearch.WordTrace tailWord_77331 prefixEnd_77331 39707972492942175806867 := by
  unfold tailWord_77331
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820493282850468928439847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1880328855233645952293231 2820493282850468928439847)
  ·
    refine ⟨4230739924275703392659771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2820493282850468928439847 4230739924275703392659771)
    ·
      refine ⟨6346109886413555088989657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230739924275703392659771 6346109886413555088989657)
      ·
        refine ⟨4759582414810166316742243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6346109886413555088989657 4759582414810166316742243)
        ·
          refine ⟨7139373622215249475113365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759582414810166316742243 7139373622215249475113365)
          ·
            refine ⟨334658138541339819145939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7139373622215249475113365 334658138541339819145939)
            ·
              refine ⟨501987207812009728718909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334658138541339819145939 501987207812009728718909)
              ·
                refine ⟨188245202929503648269591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501987207812009728718909 188245202929503648269591)
                ·
                  refine ⟨282367804394255472404387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188245202929503648269591 282367804394255472404387)
                  ·
                    refine ⟨423551706591383208606581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282367804394255472404387 423551706591383208606581)
                    ·
                      refine ⟨39707972492942175806867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 423551706591383208606581 39707972492942175806867)
                      ·
                        rfl

theorem cell23_77331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_77331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77331 prefixEnd_77331 := by exact prefixLift 77331
  have htrace : WordTrace (prefixWord ++ tailWord_77331) baseStart_77331 baseEnd_77331 := by
    simpa [prefixWord, tailWord_77331, baseEnd_77331] using wordTrace_append hprefix tailTrace_77331
  have hstable : (prefixWord ++ tailWord_77331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77331).length < 2 ^ (prefixWord ++ tailWord_77331).sum := by decide
  have hdescent : baseEnd_77331 < baseStart_77331 := by decide
  rcases family_descends (prefixWord ++ tailWord_77331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77338 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_77338 : Nat := 118140960795 + 77338 * 2 ^ 59
def prefixEnd_77338 : Nat := 4983230072969 + 3 ^ 40 * 77338 * 2
def baseEnd_77338 : Nat := 13237188952507882806445

theorem tailTrace_77338 : CollatzResearch.WordTrace tailWord_77338 prefixEnd_77338 13237188952507882806445 := by
  unfold tailWord_77338
  simp only [CollatzResearch.WordTrace]
  refine ⟨705187148456277280986167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1880499062550072749296445 705187148456277280986167)
  ·
    refine ⟨1057780722684415921479251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705187148456277280986167 1057780722684415921479251)
    ·
      refine ⟨1586671084026623882218877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057780722684415921479251 1586671084026623882218877)
      ·
        refine ⟨595001656509983955832079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1586671084026623882218877 595001656509983955832079)
        ·
          refine ⟨892502484764975933748119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595001656509983955832079 892502484764975933748119)
          ·
            refine ⟨1338753727147463900622179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892502484764975933748119 1338753727147463900622179)
            ·
              refine ⟨2008130590721195850933269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338753727147463900622179 2008130590721195850933269)
              ·
                refine ⟨94131121440056055512497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2008130590721195850933269 94131121440056055512497)
                ·
                  refine ⟨70598341080042041634373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94131121440056055512497 70598341080042041634373)
                  ·
                    refine ⟨13237188952507882806445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70598341080042041634373 13237188952507882806445)
                    ·
                      rfl

theorem cell23_77338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_77338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77338 prefixEnd_77338 := by exact prefixLift 77338
  have htrace : WordTrace (prefixWord ++ tailWord_77338) baseStart_77338 baseEnd_77338 := by
    simpa [prefixWord, tailWord_77338, baseEnd_77338] using wordTrace_append hprefix tailTrace_77338
  have hstable : (prefixWord ++ tailWord_77338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77338).length < 2 ^ (prefixWord ++ tailWord_77338).sum := by decide
  have hdescent : baseEnd_77338 < baseStart_77338 := by decide
  rcases family_descends (prefixWord ++ tailWord_77338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77341 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_77341 : Nat := 118140960795 + 77341 * 2 ^ 59
def prefixEnd_77341 : Nat := 4983230072969 + 3 ^ 40 * 77341 * 2
def baseEnd_77341 : Nat := 39713107299487136681821

theorem tailTrace_77341 : CollatzResearch.WordTrace tailWord_77341 prefixEnd_77341 39713107299487136681821 := by
  unfold tailWord_77341
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820858012814240636303877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1880572008542827090869251 2820858012814240636303877)
  ·
    refine ⟨528910877402670119306977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2820858012814240636303877 528910877402670119306977)
    ·
      refine ⟨396683158052002589480233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 528910877402670119306977 396683158052002589480233)
      ·
        refine ⟨297512368539001942110175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396683158052002589480233 297512368539001942110175)
        ·
          refine ⟨446268552808502913165263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297512368539001942110175 446268552808502913165263)
          ·
            refine ⟨669402829212754369747895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446268552808502913165263 669402829212754369747895)
            ·
              refine ⟨1004104243819131554621843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669402829212754369747895 1004104243819131554621843)
              ·
                refine ⟨1506156365728697331932765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004104243819131554621843 1506156365728697331932765)
                ·
                  refine ⟨564808637148261499474787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1506156365728697331932765 564808637148261499474787)
                  ·
                    refine ⟨847212955722392249212181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 564808637148261499474787 847212955722392249212181)
                    ·
                      refine ⟨39713107299487136681821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 847212955722392249212181 39713107299487136681821)
                      ·
                        rfl

theorem cell23_77341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_77341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77341 prefixEnd_77341 := by exact prefixLift 77341
  have htrace : WordTrace (prefixWord ++ tailWord_77341) baseStart_77341 baseEnd_77341 := by
    simpa [prefixWord, tailWord_77341, baseEnd_77341] using wordTrace_append hprefix tailTrace_77341
  have hstable : (prefixWord ++ tailWord_77341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77341).length < 2 ^ (prefixWord ++ tailWord_77341).sum := by decide
  have hdescent : baseEnd_77341 < baseStart_77341 := by decide
  rcases family_descends (prefixWord ++ tailWord_77341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77358 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_77358 : Nat := 118140960795 + 77358 * 2 ^ 59
def prefixEnd_77358 : Nat := 4983230072969 + 3 ^ 40 * 77358 * 2
def baseEnd_77358 : Nat := 39721836470613570169243

theorem tailTrace_77358 : CollatzResearch.WordTrace tailWord_77358 prefixEnd_77358 39721836470613570169243 := by
  unfold tailWord_77358
  simp only [CollatzResearch.WordTrace]
  refine ⟨352684756719081567459091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1880985369168435026448485 352684756719081567459091)
  ·
    refine ⟨529027135078622351188637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 352684756719081567459091 529027135078622351188637)
    ·
      refine ⟨198385175654483381695739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 529027135078622351188637 198385175654483381695739)
      ·
        refine ⟨297577763481725072543609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198385175654483381695739 297577763481725072543609)
        ·
          refine ⟨223183322611293804407707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297577763481725072543609 223183322611293804407707)
          ·
            refine ⟨334774983916940706611561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223183322611293804407707 334774983916940706611561)
            ·
              refine ⟨251081237937705529958671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334774983916940706611561 251081237937705529958671)
              ·
                refine ⟨376621856906558294938007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251081237937705529958671 376621856906558294938007)
                ·
                  refine ⟨564932785359837442407011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376621856906558294938007 564932785359837442407011)
                  ·
                    refine ⟨847399178039756163610517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 564932785359837442407011 847399178039756163610517)
                    ·
                      refine ⟨39721836470613570169243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 847399178039756163610517 39721836470613570169243)
                      ·
                        rfl

theorem cell23_77358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_77358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77358 prefixEnd_77358 := by exact prefixLift 77358
  have htrace : WordTrace (prefixWord ++ tailWord_77358) baseStart_77358 baseEnd_77358 := by
    simpa [prefixWord, tailWord_77358, baseEnd_77358] using wordTrace_append hprefix tailTrace_77358
  have hstable : (prefixWord ++ tailWord_77358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77358).length < 2 ^ (prefixWord ++ tailWord_77358).sum := by decide
  have hdescent : baseEnd_77358 < baseStart_77358 := by decide
  rcases family_descends (prefixWord ++ tailWord_77358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77365 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_77365 : Nat := 118140960795 + 77365 * 2 ^ 59
def prefixEnd_77365 : Nat := 4983230072969 + 3 ^ 40 * 77365 * 2
def baseEnd_77365 : Nat := 39725430835195042781711

theorem tailTrace_77365 : CollatzResearch.WordTrace tailWord_77365 prefixEnd_77365 39725430835195042781711 := by
  unfold tailWord_77365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821733364727292735177549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1881155576484861823451699 2821733364727292735177549)
  ·
    refine ⟨1058150011772734775691581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2821733364727292735177549 1058150011772734775691581)
    ·
      refine ⟨396806254414775540884343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1058150011772734775691581 396806254414775540884343)
      ·
        refine ⟨595209381622163311326515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396806254414775540884343 595209381622163311326515)
        ·
          refine ⟨892814072433244966989773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595209381622163311326515 892814072433244966989773)
          ·
            refine ⟨334805277162466862621165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 892814072433244966989773 334805277162466862621165)
            ·
              refine ⟨125551978935925073482937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334805277162466862621165 125551978935925073482937)
              ·
                refine ⟨94163984201943805112203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125551978935925073482937 94163984201943805112203)
                ·
                  refine ⟨141245976302915707668305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94163984201943805112203 141245976302915707668305)
                  ·
                    refine ⟨105934482227186780751229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141245976302915707668305 105934482227186780751229)
                    ·
                      refine ⟨39725430835195042781711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 105934482227186780751229 39725430835195042781711)
                      ·
                        rfl

theorem cell23_77365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_77365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77365 prefixEnd_77365 := by exact prefixLift 77365
  have htrace : WordTrace (prefixWord ++ tailWord_77365) baseStart_77365 baseEnd_77365 := by
    simpa [prefixWord, tailWord_77365, baseEnd_77365] using wordTrace_append hprefix tailTrace_77365
  have hstable : (prefixWord ++ tailWord_77365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77365).length < 2 ^ (prefixWord ++ tailWord_77365).sum := by decide
  have hdescent : baseEnd_77365 < baseStart_77365 := by decide
  rcases family_descends (prefixWord ++ tailWord_77365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77411 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 8]
def baseStart_77411 : Nat := 118140960795 + 77411 * 2 ^ 59
def prefixEnd_77411 : Nat := 4983230072969 + 3 ^ 40 * 77411 * 2
def baseEnd_77411 : Nat := 13249683648433954268833

theorem tailTrace_77411 : CollatzResearch.WordTrace tailWord_77411 prefixEnd_77411 13249683648433954268833 := by
  unfold tailWord_77411
  simp only [CollatzResearch.WordTrace]
  refine ⟨2823411122560642591352087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1882274081707095060901391 2823411122560642591352087)
  ·
    refine ⟨4235116683840963887028131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2823411122560642591352087 4235116683840963887028131)
    ·
      refine ⟨6352675025761445830542197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235116683840963887028131 6352675025761445830542197)
      ·
        refine ⟨595563283665135546613331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6352675025761445830542197 595563283665135546613331)
        ·
          refine ⟨893344925497703319919997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595563283665135546613331 893344925497703319919997)
          ·
            refine ⟨335004347061638744969999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 893344925497703319919997 335004347061638744969999)
            ·
              refine ⟨502506520592458117454999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335004347061638744969999 502506520592458117454999)
              ·
                refine ⟨753759780888687176182499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502506520592458117454999 753759780888687176182499)
                ·
                  refine ⟨1130639671333030764273749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753759780888687176182499 1130639671333030764273749)
                  ·
                    refine ⟨13249683648433954268833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1130639671333030764273749 13249683648433954268833)
                    ·
                      rfl

theorem cell23_77411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 8].length) (baseStart_77411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77411 prefixEnd_77411 := by exact prefixLift 77411
  have htrace : WordTrace (prefixWord ++ tailWord_77411) baseStart_77411 baseEnd_77411 := by
    simpa [prefixWord, tailWord_77411, baseEnd_77411] using wordTrace_append hprefix tailTrace_77411
  have hstable : (prefixWord ++ tailWord_77411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77411).length < 2 ^ (prefixWord ++ tailWord_77411).sum := by decide
  have hdescent : baseEnd_77411 < baseStart_77411 := by decide
  rcases family_descends (prefixWord ++ tailWord_77411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77431 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_77431 : Nat := 118140960795 + 77431 * 2 ^ 59
def prefixEnd_77431 : Nat := 4983230072969 + 3 ^ 40 * 77431 * 2
def baseEnd_77431 : Nat := 39759320558391784556407

theorem tailTrace_77431 : CollatzResearch.WordTrace tailWord_77431 prefixEnd_77431 39759320558391784556407 := by
  unfold tailWord_77431
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824140582488186007080147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1882760388325457338053431 2824140582488186007080147)
  ·
    refine ⟨4236210873732279010620221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824140582488186007080147 4236210873732279010620221)
    ·
      refine ⟨1588579077649604628982583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4236210873732279010620221 1588579077649604628982583)
      ·
        refine ⟨2382868616474406943473875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588579077649604628982583 2382868616474406943473875)
        ·
          refine ⟨3574302924711610415210813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382868616474406943473875 3574302924711610415210813)
          ·
            refine ⟨1340363596766853905704055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3574302924711610415210813 1340363596766853905704055)
            ·
              refine ⟨2010545395150280858556083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340363596766853905704055 2010545395150280858556083)
              ·
                refine ⟨3015818092725421287834125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010545395150280858556083 3015818092725421287834125)
                ·
                  refine ⟨1130931784772032982937797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3015818092725421287834125 1130931784772032982937797)
                  ·
                    refine ⟨212049709644756184300837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1130931784772032982937797 212049709644756184300837)
                    ·
                      refine ⟨39759320558391784556407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 212049709644756184300837 39759320558391784556407)
                      ·
                        rfl

theorem cell23_77431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_77431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77431 prefixEnd_77431 := by exact prefixLift 77431
  have htrace : WordTrace (prefixWord ++ tailWord_77431) baseStart_77431 baseEnd_77431 := by
    simpa [prefixWord, tailWord_77431, baseEnd_77431] using wordTrace_append hprefix tailTrace_77431
  have hstable : (prefixWord ++ tailWord_77431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77431).length < 2 ^ (prefixWord ++ tailWord_77431).sum := by decide
  have hdescent : baseEnd_77431 < baseStart_77431 := by decide
  rcases family_descends (prefixWord ++ tailWord_77431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77435 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 4, 2, 2]
def baseStart_77435 : Nat := 118140960795 + 77435 * 2 ^ 59
def prefixEnd_77435 : Nat := 4983230072969 + 3 ^ 40 * 77435 * 2
def baseEnd_77435 : Nat := 39761374481009768906389

theorem tailTrace_77435 : CollatzResearch.WordTrace tailWord_77435 prefixEnd_77435 39761374481009768906389 := by
  unfold tailWord_77435
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824286474473694690225759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1882857649649129793483839 2824286474473694690225759)
  ·
    refine ⟨4236429711710542035338639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824286474473694690225759 4236429711710542035338639)
    ·
      refine ⟨6354644567565813053007959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236429711710542035338639 6354644567565813053007959)
      ·
        refine ⟨9531966851348719579511939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354644567565813053007959 9531966851348719579511939)
        ·
          refine ⟨14297950277023079369267909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531966851348719579511939 14297950277023079369267909)
          ·
            refine ⟨2680865676941827381737733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14297950277023079369267909 2680865676941827381737733)
            ·
              refine ⟨502662314426592634075825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2680865676941827381737733 502662314426592634075825)
              ·
                refine ⟨376996735819944475556869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502662314426592634075825 376996735819944475556869)
                ·
                  refine ⟨70686887966239589166913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376996735819944475556869 70686887966239589166913)
                  ·
                    refine ⟨53015165974679691875185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70686887966239589166913 53015165974679691875185)
                    ·
                      refine ⟨39761374481009768906389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53015165974679691875185 39761374481009768906389)
                      ·
                        rfl

theorem cell23_77435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 2, 2].length) (baseStart_77435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77435 prefixEnd_77435 := by exact prefixLift 77435
  have htrace : WordTrace (prefixWord ++ tailWord_77435) baseStart_77435 baseEnd_77435 := by
    simpa [prefixWord, tailWord_77435, baseEnd_77435] using wordTrace_append hprefix tailTrace_77435
  have hstable : (prefixWord ++ tailWord_77435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77435).length < 2 ^ (prefixWord ++ tailWord_77435).sum := by decide
  have hdescent : baseEnd_77435 < baseStart_77435 := by decide
  rcases family_descends (prefixWord ++ tailWord_77435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77569 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 1, 4]
def baseStart_77569 : Nat := 118140960795 + 77569 * 2 ^ 59
def prefixEnd_77569 : Nat := 4983230072969 + 3 ^ 40 * 77569 * 2
def baseEnd_77569 : Nat := 13276726962904081543591

theorem tailTrace_77569 : CollatzResearch.WordTrace tailWord_77569 prefixEnd_77569 13276726962904081543591 := by
  unfold tailWord_77569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829173855988235575603761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1886115903992157050402507 2829173855988235575603761)
  ·
    refine ⟨2121880391991176681702821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2829173855988235575603761 2121880391991176681702821)
    ·
      refine ⟨397852573498345627819279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2121880391991176681702821 397852573498345627819279)
      ·
        refine ⟨596778860247518441728919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397852573498345627819279 596778860247518441728919)
        ·
          refine ⟨895168290371277662593379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596778860247518441728919 895168290371277662593379)
          ·
            refine ⟨1342752435556916493890069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895168290371277662593379 1342752435556916493890069)
            ·
              refine ⟨62941520416730460651097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1342752435556916493890069 62941520416730460651097)
              ·
                refine ⟨47206140312547845488323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62941520416730460651097 47206140312547845488323)
                ·
                  refine ⟨70809210468821768232485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47206140312547845488323 70809210468821768232485)
                  ·
                    refine ⟨13276726962904081543591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70809210468821768232485 13276726962904081543591)
                    ·
                      rfl

theorem cell23_77569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_77569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77569 prefixEnd_77569 := by exact prefixLift 77569
  have htrace : WordTrace (prefixWord ++ tailWord_77569) baseStart_77569 baseEnd_77569 := by
    simpa [prefixWord, tailWord_77569, baseEnd_77569] using wordTrace_append hprefix tailTrace_77569
  have hstable : (prefixWord ++ tailWord_77569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77569).length < 2 ^ (prefixWord ++ tailWord_77569).sum := by decide
  have hdescent : baseEnd_77569 < baseStart_77569 := by decide
  rcases family_descends (prefixWord ++ tailWord_77569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77585 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 1, 5, 2]
def baseStart_77585 : Nat := 118140960795 + 77585 * 2 ^ 59
def prefixEnd_77585 : Nat := 4983230072969 + 3 ^ 40 * 77585 * 2
def baseEnd_77585 : Nat := 39838396579184182030699

theorem tailTrace_77585 : CollatzResearch.WordTrace tailWord_77585 prefixEnd_77585 39838396579184182030699 := by
  unfold tailWord_77585
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829757423930270308186209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1886504949286846872124139 2829757423930270308186209)
  ·
    refine ⟨2122318067947702731139657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2829757423930270308186209 2122318067947702731139657)
    ·
      refine ⟨1591738550960777048354743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2122318067947702731139657 1591738550960777048354743)
      ·
        refine ⟨2387607826441165572532115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591738550960777048354743 2387607826441165572532115)
        ·
          refine ⟨3581411739661748358798173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2387607826441165572532115 3581411739661748358798173)
          ·
            refine ⟨1343029402373155634549315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3581411739661748358798173 1343029402373155634549315)
            ·
              refine ⟨2014544103559733451823973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343029402373155634549315 2014544103559733451823973)
              ·
                refine ⟨377727019417450022216995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2014544103559733451823973 377727019417450022216995)
                ·
                  refine ⟨566590529126175033325493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377727019417450022216995 566590529126175033325493)
                  ·
                    refine ⟨53117862105578909374265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 566590529126175033325493 53117862105578909374265)
                    ·
                      refine ⟨39838396579184182030699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53117862105578909374265 39838396579184182030699)
                      ·
                        rfl

theorem cell23_77585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_77585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77585 prefixEnd_77585 := by exact prefixLift 77585
  have htrace : WordTrace (prefixWord ++ tailWord_77585) baseStart_77585 baseEnd_77585 := by
    simpa [prefixWord, tailWord_77585, baseEnd_77585] using wordTrace_append hprefix tailTrace_77585
  have hstable : (prefixWord ++ tailWord_77585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77585).length < 2 ^ (prefixWord ++ tailWord_77585).sum := by decide
  have hdescent : baseEnd_77585 < baseStart_77585 := by decide
  rcases family_descends (prefixWord ++ tailWord_77585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77602 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_77602 : Nat := 118140960795 + 77602 * 2 ^ 59
def prefixEnd_77602 : Nat := 4983230072969 + 3 ^ 40 * 77602 * 2
def baseEnd_77602 : Nat := 39847125750310615518121

theorem tailTrace_77602 : CollatzResearch.WordTrace tailWord_77602 prefixEnd_77602 39847125750310615518121 := by
  unfold tailWord_77602
  simp only [CollatzResearch.WordTrace]
  refine ⟨707594366217170552888765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1886918309912454807703373 707594366217170552888765)
  ·
    refine ⟨265347887331438957333287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 707594366217170552888765 265347887331438957333287)
    ·
      refine ⟨398021830997158435999931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265347887331438957333287 398021830997158435999931)
      ·
        refine ⟨597032746495737653999897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398021830997158435999931 597032746495737653999897)
        ·
          refine ⟨447774559871803240499923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597032746495737653999897 447774559871803240499923)
          ·
            refine ⟨671661839807704860749885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447774559871803240499923 671661839807704860749885)
            ·
              refine ⟨251873189927889322781207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 671661839807704860749885 251873189927889322781207)
              ·
                refine ⟨377809784891833984171811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251873189927889322781207 377809784891833984171811)
                ·
                  refine ⟨566714677337750976257717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377809784891833984171811 566714677337750976257717)
                  ·
                    refine ⟨53129501000414154024161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 566714677337750976257717 53129501000414154024161)
                    ·
                      refine ⟨39847125750310615518121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53129501000414154024161 39847125750310615518121)
                      ·
                        rfl

theorem cell23_77602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_77602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77602 prefixEnd_77602 := by exact prefixLift 77602
  have htrace : WordTrace (prefixWord ++ tailWord_77602) baseStart_77602 baseEnd_77602 := by
    simpa [prefixWord, tailWord_77602, baseEnd_77602] using wordTrace_append hprefix tailTrace_77602
  have hstable : (prefixWord ++ tailWord_77602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77602).length < 2 ^ (prefixWord ++ tailWord_77602).sum := by decide
  have hdescent : baseEnd_77602 < baseStart_77602 := by decide
  rcases family_descends (prefixWord ++ tailWord_77602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77612 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_77612 : Nat := 118140960795 + 77612 * 2 ^ 59
def prefixEnd_77612 : Nat := 4983230072969 + 3 ^ 40 * 77612 * 2
def baseEnd_77612 : Nat := 13284086852285192131025

theorem tailTrace_77612 : CollatzResearch.WordTrace tailWord_77612 prefixEnd_77612 13284086852285192131025 := by
  unfold tailWord_77612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415371097416226959709545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1887161463221635946279393 1415371097416226959709545)
  ·
    refine ⟨1061528323062170219782159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1415371097416226959709545 1061528323062170219782159)
    ·
      refine ⟨1592292484593255329673239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061528323062170219782159 1592292484593255329673239)
      ·
        refine ⟨2388438726889882994509859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592292484593255329673239 2388438726889882994509859)
        ·
          refine ⟨3582658090334824491764789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388438726889882994509859 3582658090334824491764789)
          ·
            refine ⟨335874195968889796102949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3582658090334824491764789 335874195968889796102949)
            ·
              refine ⟨62976411744166836769303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 335874195968889796102949 62976411744166836769303)
              ·
                refine ⟨94464617616250255153955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62976411744166836769303 94464617616250255153955)
                ·
                  refine ⟨141696926424375382730933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94464617616250255153955 141696926424375382730933)
                  ·
                    refine ⟨13284086852285192131025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 141696926424375382730933 13284086852285192131025)
                    ·
                      rfl

theorem cell23_77612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_77612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77612 prefixEnd_77612 := by exact prefixLift 77612
  have htrace : WordTrace (prefixWord ++ tailWord_77612) baseStart_77612 baseEnd_77612 := by
    simpa [prefixWord, tailWord_77612, baseEnd_77612] using wordTrace_append hprefix tailTrace_77612
  have hstable : (prefixWord ++ tailWord_77612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77612).length < 2 ^ (prefixWord ++ tailWord_77612).sum := by decide
  have hdescent : baseEnd_77612 < baseStart_77612 := by decide
  rcases family_descends (prefixWord ++ tailWord_77612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77615 : List Nat := [1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 4]
def baseStart_77615 : Nat := 118140960795 + 77615 * 2 ^ 59
def prefixEnd_77615 : Nat := 4983230072969 + 3 ^ 40 * 77615 * 2
def baseEnd_77615 : Nat := 39853800998819064655561

theorem tailTrace_77615 : CollatzResearch.WordTrace tailWord_77615 prefixEnd_77615 39853800998819064655561 := by
  unfold tailWord_77615
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830851613821585431778299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1887234409214390287852199 2830851613821585431778299)
  ·
    refine ⟨4246277420732378147667449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2830851613821585431778299 4246277420732378147667449)
    ·
      refine ⟨3184708065549283610750587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4246277420732378147667449 3184708065549283610750587)
      ·
        refine ⟨4777062098323925416125881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184708065549283610750587 4777062098323925416125881)
        ·
          refine ⟨3582796573742944062094411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4777062098323925416125881 3582796573742944062094411)
          ·
            refine ⟨5374194860614416093141617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582796573742944062094411 5374194860614416093141617)
            ·
              refine ⟨4030646145460812069856213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5374194860614416093141617 4030646145460812069856213)
              ·
                refine ⟨94468269034237782887255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4030646145460812069856213 94468269034237782887255)
                ·
                  refine ⟨141702403551356674330883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94468269034237782887255 141702403551356674330883)
                  ·
                    refine ⟨212553605327035011496325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141702403551356674330883 212553605327035011496325)
                    ·
                      refine ⟨39853800998819064655561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 212553605327035011496325 39853800998819064655561)
                      ·
                        rfl

theorem cell23_77615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_77615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77615 prefixEnd_77615 := by exact prefixLift 77615
  have htrace : WordTrace (prefixWord ++ tailWord_77615) baseStart_77615 baseEnd_77615 := by
    simpa [prefixWord, tailWord_77615, baseEnd_77615] using wordTrace_append hprefix tailTrace_77615
  have hstable : (prefixWord ++ tailWord_77615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77615).length < 2 ^ (prefixWord ++ tailWord_77615).sum := by decide
  have hdescent : baseEnd_77615 < baseStart_77615 := by decide
  rcases family_descends (prefixWord ++ tailWord_77615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77635 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5]
def baseStart_77635 : Nat := 118140960795 + 77635 * 2 ^ 59
def prefixEnd_77635 : Nat := 4983230072969 + 3 ^ 40 * 77635 * 2
def baseEnd_77635 : Nat := 39864070611908986405469

theorem tailTrace_77635 : CollatzResearch.WordTrace tailWord_77635 prefixEnd_77635 39864070611908986405469 := by
  unfold tailWord_77635
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831581073749128847506359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1887720715832752565004239 2831581073749128847506359)
  ·
    refine ⟨4247371610623693271259539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2831581073749128847506359 4247371610623693271259539)
    ·
      refine ⟨6371057415935539906889309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247371610623693271259539 6371057415935539906889309)
      ·
        refine ⟨2389146530975827465083491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6371057415935539906889309 2389146530975827465083491)
        ·
          refine ⟨3583719796463741197625237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389146530975827465083491 3583719796463741197625237)
          ·
            refine ⟨167986865459237868638683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3583719796463741197625237 167986865459237868638683)
            ·
              refine ⟨251980298188856802958025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167986865459237868638683 251980298188856802958025)
              ·
                refine ⟨188985223641642602218519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251980298188856802958025 188985223641642602218519)
                ·
                  refine ⟨283477835462463903327779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188985223641642602218519 283477835462463903327779)
                  ·
                    refine ⟨425216753193695854991669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 283477835462463903327779 425216753193695854991669)
                    ·
                      refine ⟨39864070611908986405469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 425216753193695854991669 39864070611908986405469)
                      ·
                        rfl

theorem cell23_77635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_77635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77635 prefixEnd_77635 := by exact prefixLift 77635
  have htrace : WordTrace (prefixWord ++ tailWord_77635) baseStart_77635 baseEnd_77635 := by
    simpa [prefixWord, tailWord_77635, baseEnd_77635] using wordTrace_append hprefix tailTrace_77635
  have hstable : (prefixWord ++ tailWord_77635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77635).length < 2 ^ (prefixWord ++ tailWord_77635).sum := by decide
  have hdescent : baseEnd_77635 < baseStart_77635 := by decide
  rcases family_descends (prefixWord ++ tailWord_77635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77649 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 3, 2, 2]
def baseStart_77649 : Nat := 118140960795 + 77649 * 2 ^ 59
def prefixEnd_77649 : Nat := 4983230072969 + 3 ^ 40 * 77649 * 2
def baseEnd_77649 : Nat := 39871259341071931630405

theorem tailTrace_77649 : CollatzResearch.WordTrace tailWord_77649 prefixEnd_77649 39871259341071931630405 := by
  unfold tailWord_77649
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832091695698409238516001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888061130465606159010667 2832091695698409238516001)
  ·
    refine ⟨2124068771773806928887001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2832091695698409238516001 2124068771773806928887001)
    ·
      refine ⟨1593051578830355196665251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2124068771773806928887001 1593051578830355196665251)
      ·
        refine ⟨2389577368245532794997877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593051578830355196665251 2389577368245532794997877)
        ·
          refine ⟨224022878273018699531051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2389577368245532794997877 224022878273018699531051)
          ·
            refine ⟨336034317409528049296577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224022878273018699531051 336034317409528049296577)
            ·
              refine ⟨252025738057146036972433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336034317409528049296577 252025738057146036972433)
              ·
                refine ⟨189019303542859527729325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252025738057146036972433 189019303542859527729325)
                ·
                  refine ⟨70882238828572322898497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189019303542859527729325 70882238828572322898497)
                  ·
                    refine ⟨53161679121429242173873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70882238828572322898497 53161679121429242173873)
                    ·
                      refine ⟨39871259341071931630405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53161679121429242173873 39871259341071931630405)
                      ·
                        rfl

theorem cell23_77649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_77649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77649 prefixEnd_77649 := by exact prefixLift 77649
  have htrace : WordTrace (prefixWord ++ tailWord_77649) baseStart_77649 baseEnd_77649 := by
    simpa [prefixWord, tailWord_77649, baseEnd_77649] using wordTrace_append hprefix tailTrace_77649
  have hstable : (prefixWord ++ tailWord_77649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77649).length < 2 ^ (prefixWord ++ tailWord_77649).sum := by decide
  have hdescent : baseEnd_77649 < baseStart_77649 := by decide
  rcases family_descends (prefixWord ++ tailWord_77649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77655 : List Nat := [1, 1, 3, 2, 5, 1, 1, 9]
def baseStart_77655 : Nat := 118140960795 + 77655 * 2 ^ 59
def prefixEnd_77655 : Nat := 4983230072969 + 3 ^ 40 * 77655 * 2
def baseEnd_77655 : Nat := 1476827415740700302051

theorem tailTrace_77655 : CollatzResearch.WordTrace tailWord_77655 prefixEnd_77655 1476827415740700302051 := by
  unfold tailWord_77655
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832310533676672263234419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888207022451114842156279 2832310533676672263234419)
  ·
    refine ⟨4248465800515008394851629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2832310533676672263234419 4248465800515008394851629)
    ·
      refine ⟨1593174675193128148069361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4248465800515008394851629 1593174675193128148069361)
      ·
        refine ⟨1194881006394846111052021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1593174675193128148069361 1194881006394846111052021)
        ·
          refine ⟨112020094349516822911127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1194881006394846111052021 112020094349516822911127)
          ·
            refine ⟨168030141524275234366691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112020094349516822911127 168030141524275234366691)
            ·
              refine ⟨252045212286412851550037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168030141524275234366691 252045212286412851550037)
              ·
                refine ⟨1476827415740700302051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 252045212286412851550037 1476827415740700302051)
                ·
                  rfl

theorem cell23_77655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 9].length) (baseStart_77655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77655 prefixEnd_77655 := by exact prefixLift 77655
  have htrace : WordTrace (prefixWord ++ tailWord_77655) baseStart_77655 baseEnd_77655 := by
    simpa [prefixWord, tailWord_77655, baseEnd_77655] using wordTrace_append hprefix tailTrace_77655
  have hstable : (prefixWord ++ tailWord_77655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77655).length < 2 ^ (prefixWord ++ tailWord_77655).sum := by decide
  have hdescent : baseEnd_77655 < baseStart_77655 := by decide
  rcases family_descends (prefixWord ++ tailWord_77655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77660 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_77660 : Nat := 118140960795 + 77660 * 2 ^ 59
def prefixEnd_77660 : Nat := 4983230072969 + 3 ^ 40 * 77660 * 2
def baseEnd_77660 : Nat := 39876907628271388592855

theorem tailTrace_77660 : CollatzResearch.WordTrace tailWord_77660 prefixEnd_77660 39876907628271388592855 := by
  unfold tailWord_77660
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416246449329279058583217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1888328599105705411444289 1416246449329279058583217)
  ·
    refine ⟨1062184836996959293937413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1416246449329279058583217 1062184836996959293937413)
    ·
      refine ⟨199159656936929867613265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1062184836996959293937413 199159656936929867613265)
      ·
        refine ⟨149369742702697400709949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199159656936929867613265 149369742702697400709949)
        ·
          refine ⟨56013653513511525266231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149369742702697400709949 56013653513511525266231)
          ·
            refine ⟨84020480270267287899347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56013653513511525266231 84020480270267287899347)
            ·
              refine ⟨126030720405400931849021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84020480270267287899347 126030720405400931849021)
              ·
                refine ⟨47261520152025349443383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126030720405400931849021 47261520152025349443383)
                ·
                  refine ⟨70892280228038024165075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47261520152025349443383 70892280228038024165075)
                  ·
                    refine ⟨106338420342057036247613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70892280228038024165075 106338420342057036247613)
                    ·
                      refine ⟨39876907628271388592855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106338420342057036247613 39876907628271388592855)
                      ·
                        rfl

theorem cell23_77660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_77660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77660 prefixEnd_77660 := by exact prefixLift 77660
  have htrace : WordTrace (prefixWord ++ tailWord_77660) baseStart_77660 baseEnd_77660 := by
    simpa [prefixWord, tailWord_77660, baseEnd_77660] using wordTrace_append hprefix tailTrace_77660
  have hstable : (prefixWord ++ tailWord_77660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77660).length < 2 ^ (prefixWord ++ tailWord_77660).sum := by decide
  have hdescent : baseEnd_77660 < baseStart_77660 := by decide
  rcases family_descends (prefixWord ++ tailWord_77660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77665 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_77665 : Nat := 118140960795 + 77665 * 2 ^ 59
def prefixEnd_77665 : Nat := 4983230072969 + 3 ^ 40 * 77665 * 2
def baseEnd_77665 : Nat := 39879475031543869030331

theorem tailTrace_77665 : CollatzResearch.WordTrace tailWord_77665 prefixEnd_77665 39879475031543869030331 := by
  unfold tailWord_77665
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832675263640443971098449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888450175760295980732299 2832675263640443971098449)
  ·
    refine ⟨2124506447730332978323837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2832675263640443971098449 2124506447730332978323837)
    ·
      refine ⟨796689917898874866871439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2124506447730332978323837 796689917898874866871439)
      ·
        refine ⟨1195034876848312300307159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796689917898874866871439 1195034876848312300307159)
        ·
          refine ⟨1792552315272468450460739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195034876848312300307159 1792552315272468450460739)
          ·
            refine ⟨2688828472908702675691109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792552315272468450460739 2688828472908702675691109)
            ·
              refine ⟨504155338670381751692083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2688828472908702675691109 504155338670381751692083)
              ·
                refine ⟨756233008005572627538125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504155338670381751692083 756233008005572627538125)
                ·
                  refine ⟨283587378002089735326797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756233008005572627538125 283587378002089735326797)
                  ·
                    refine ⟨106345266750783650747549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283587378002089735326797 106345266750783650747549)
                    ·
                      refine ⟨39879475031543869030331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106345266750783650747549 39879475031543869030331)
                      ·
                        rfl

theorem cell23_77665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_77665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77665 prefixEnd_77665 := by exact prefixLift 77665
  have htrace : WordTrace (prefixWord ++ tailWord_77665) baseStart_77665 baseEnd_77665 := by
    simpa [prefixWord, tailWord_77665, baseEnd_77665] using wordTrace_append hprefix tailTrace_77665
  have hstable : (prefixWord ++ tailWord_77665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77665).length < 2 ^ (prefixWord ++ tailWord_77665).sum := by decide
  have hdescent : baseEnd_77665 < baseStart_77665 := by decide
  rcases family_descends (prefixWord ++ tailWord_77665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77685 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_77685 : Nat := 118140960795 + 77685 * 2 ^ 59
def prefixEnd_77685 : Nat := 4983230072969 + 3 ^ 40 * 77685 * 2
def baseEnd_77685 : Nat := 13296581548211263593413

theorem tailTrace_77685 : CollatzResearch.WordTrace tailWord_77685 prefixEnd_77685 13296581548211263593413 := by
  unfold tailWord_77685
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833404723567987386826509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1888936482378658257884339 2833404723567987386826509)
  ·
    refine ⟨1062526771337995270059941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2833404723567987386826509 1062526771337995270059941)
    ·
      refine ⟨199223769625874113136239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1062526771337995270059941 199223769625874113136239)
      ·
        refine ⟨298835654438811169704359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199223769625874113136239 298835654438811169704359)
        ·
          refine ⟨448253481658216754556539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298835654438811169704359 448253481658216754556539)
          ·
            refine ⟨672380222487325131834809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448253481658216754556539 672380222487325131834809)
            ·
              refine ⟨504285166865493848876107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672380222487325131834809 504285166865493848876107)
              ·
                refine ⟨756427750298240773314161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504285166865493848876107 756427750298240773314161)
                ·
                  refine ⟨567320812723680579985621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756427750298240773314161 567320812723680579985621)
                  ·
                    refine ⟨13296581548211263593413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 567320812723680579985621 13296581548211263593413)
                    ·
                      rfl

theorem cell23_77685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_77685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77685 prefixEnd_77685 := by exact prefixLift 77685
  have htrace : WordTrace (prefixWord ++ tailWord_77685) baseStart_77685 baseEnd_77685 := by
    simpa [prefixWord, tailWord_77685, baseEnd_77685] using wordTrace_append hprefix tailTrace_77685
  have hstable : (prefixWord ++ tailWord_77685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77685).length < 2 ^ (prefixWord ++ tailWord_77685).sum := by decide
  have hdescent : baseEnd_77685 < baseStart_77685 := by decide
  rcases family_descends (prefixWord ++ tailWord_77685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77688 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_77688 : Nat := 118140960795 + 77688 * 2 ^ 59
def prefixEnd_77688 : Nat := 4983230072969 + 3 ^ 40 * 77688 * 2
def baseEnd_77688 : Nat := 39891285086597279042725

theorem tailTrace_77688 : CollatzResearch.WordTrace tailWord_77688 prefixEnd_77688 39891285086597279042725 := by
  unfold tailWord_77688
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416757071278559449592859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1889009428371412599457145 1416757071278559449592859)
  ·
    refine ⟨2125135606917839174389289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1416757071278559449592859 2125135606917839174389289)
    ·
      refine ⟨1593851705188379380791967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125135606917839174389289 1593851705188379380791967)
      ·
        refine ⟨2390777557782569071187951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593851705188379380791967 2390777557782569071187951)
        ·
          refine ⟨3586166336673853606781927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390777557782569071187951 3586166336673853606781927)
          ·
            refine ⟨5379249505010780410172891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586166336673853606781927 5379249505010780410172891)
            ·
              refine ⟨8068874257516170615259337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379249505010780410172891 8068874257516170615259337)
              ·
                refine ⟨6051655693137127961444503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8068874257516170615259337 6051655693137127961444503)
                ·
                  refine ⟨9077483539705691942166755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051655693137127961444503 9077483539705691942166755)
                  ·
                    refine ⟨13616225309558537913250133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9077483539705691942166755 13616225309558537913250133)
                    ·
                      refine ⟨39891285086597279042725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 13616225309558537913250133 39891285086597279042725)
                      ·
                        rfl

theorem cell23_77688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_77688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77688 prefixEnd_77688 := by exact prefixLift 77688
  have htrace : WordTrace (prefixWord ++ tailWord_77688) baseStart_77688 baseEnd_77688 := by
    simpa [prefixWord, tailWord_77688, baseEnd_77688] using wordTrace_append hprefix tailTrace_77688
  have hstable : (prefixWord ++ tailWord_77688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77688).length < 2 ^ (prefixWord ++ tailWord_77688).sum := by decide
  have hdescent : baseEnd_77688 < baseStart_77688 := by decide
  rcases family_descends (prefixWord ++ tailWord_77688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77699 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 3]
def baseStart_77699 : Nat := 118140960795 + 77699 * 2 ^ 59
def prefixEnd_77699 : Nat := 4983230072969 + 3 ^ 40 * 77699 * 2
def baseEnd_77699 : Nat := 39896933373796736005175

theorem tailTrace_77699 : CollatzResearch.WordTrace tailWord_77699 prefixEnd_77699 39896933373796736005175 := by
  unfold tailWord_77699
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833915345517267777836151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1889276897011511851890767 2833915345517267777836151)
  ·
    refine ⟨4250873018275901666754227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2833915345517267777836151 4250873018275901666754227)
    ·
      refine ⟨6376309527413852500131341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4250873018275901666754227 6376309527413852500131341)
      ·
        refine ⟨2391116072780194687549253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6376309527413852500131341 2391116072780194687549253)
        ·
          refine ⟨448334263646286503915485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2391116072780194687549253 448334263646286503915485)
          ·
            refine ⟨168125348867357438968307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 448334263646286503915485 168125348867357438968307)
            ·
              refine ⟨252188023301036158452461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168125348867357438968307 252188023301036158452461)
              ·
                refine ⟨94570508737888559419673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252188023301036158452461 94570508737888559419673)
                ·
                  refine ⟨70927881553416419564755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94570508737888559419673 70927881553416419564755)
                  ·
                    refine ⟨106391822330124629347133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70927881553416419564755 106391822330124629347133)
                    ·
                      refine ⟨39896933373796736005175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106391822330124629347133 39896933373796736005175)
                      ·
                        rfl

theorem cell23_77699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_77699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77699 prefixEnd_77699 := by exact prefixLift 77699
  have htrace : WordTrace (prefixWord ++ tailWord_77699) baseStart_77699 baseEnd_77699 := by
    simpa [prefixWord, tailWord_77699, baseEnd_77699] using wordTrace_append hprefix tailTrace_77699
  have hstable : (prefixWord ++ tailWord_77699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77699).length < 2 ^ (prefixWord ++ tailWord_77699).sum := by decide
  have hdescent : baseEnd_77699 < baseStart_77699 := by decide
  rcases family_descends (prefixWord ++ tailWord_77699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77755 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 3]
def baseStart_77755 : Nat := 118140960795 + 77755 * 2 ^ 59
def prefixEnd_77755 : Nat := 4983230072969 + 3 ^ 40 * 77755 * 2
def baseEnd_77755 : Nat := 39925688290448516904917

theorem tailTrace_77755 : CollatzResearch.WordTrace tailWord_77755 prefixEnd_77755 39925688290448516904917 := by
  unfold tailWord_77755
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835957833314389341874719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1890638555542926227916479 2835957833314389341874719)
  ·
    refine ⟨4253936749971584012812079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835957833314389341874719 4253936749971584012812079)
    ·
      refine ⟨6380905124957376019218119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253936749971584012812079 6380905124957376019218119)
      ·
        refine ⟨9571357687436064028827179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6380905124957376019218119 9571357687436064028827179)
        ·
          refine ⟨14357036531154096043240769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9571357687436064028827179 14357036531154096043240769)
          ·
            refine ⟨10767777398365572032430577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14357036531154096043240769 10767777398365572032430577)
            ·
              refine ⟨8075833048774179024322933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10767777398365572032430577 8075833048774179024322933)
              ·
                refine ⟨757109348322579283530275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8075833048774179024322933 757109348322579283530275)
                ·
                  refine ⟨1135664022483868925295413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757109348322579283530275 1135664022483868925295413)
                  ·
                    refine ⟨106468502107862711746445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1135664022483868925295413 106468502107862711746445)
                    ·
                      refine ⟨39925688290448516904917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106468502107862711746445 39925688290448516904917)
                      ·
                        rfl

theorem cell23_77755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 3].length) (baseStart_77755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77755 prefixEnd_77755 := by exact prefixLift 77755
  have htrace : WordTrace (prefixWord ++ tailWord_77755) baseStart_77755 baseEnd_77755 := by
    simpa [prefixWord, tailWord_77755, baseEnd_77755] using wordTrace_append hprefix tailTrace_77755
  have hstable : (prefixWord ++ tailWord_77755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77755).length < 2 ^ (prefixWord ++ tailWord_77755).sum := by decide
  have hdescent : baseEnd_77755 < baseStart_77755 := by decide
  rcases family_descends (prefixWord ++ tailWord_77755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77775 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 1, 7]
def baseStart_77775 : Nat := 118140960795 + 77775 * 2 ^ 59
def prefixEnd_77775 : Nat := 4983230072969 + 3 ^ 40 * 77775 * 2
def baseEnd_77775 : Nat := 13311985967846146218275

theorem tailTrace_77775 : CollatzResearch.WordTrace tailWord_77775 prefixEnd_77775 13311985967846146218275 := by
  unfold tailWord_77775
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836687293241932757602779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1891124862161288505068519 2836687293241932757602779)
  ·
    refine ⟨4255030939862899136404169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2836687293241932757602779 4255030939862899136404169)
    ·
      refine ⟨3191273204897174352303127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4255030939862899136404169 3191273204897174352303127)
      ·
        refine ⟨4786909807345761528454691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191273204897174352303127 4786909807345761528454691)
        ·
          refine ⟨7180364711018642292682037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786909807345761528454691 7180364711018642292682037)
          ·
            refine ⟨673159191657997714938941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7180364711018642292682037 673159191657997714938941)
            ·
              refine ⟨252434696871749143102103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673159191657997714938941 252434696871749143102103)
              ·
                refine ⟨378652045307623714653155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252434696871749143102103 378652045307623714653155)
                ·
                  refine ⟨567978067961435571979733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378652045307623714653155 567978067961435571979733)
                  ·
                    refine ⟨13311985967846146218275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 567978067961435571979733 13311985967846146218275)
                    ·
                      rfl

theorem cell23_77775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_77775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77775 prefixEnd_77775 := by exact prefixLift 77775
  have htrace : WordTrace (prefixWord ++ tailWord_77775) baseStart_77775 baseEnd_77775 := by
    simpa [prefixWord, tailWord_77775, baseEnd_77775] using wordTrace_append hprefix tailTrace_77775
  have hstable : (prefixWord ++ tailWord_77775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77775).length < 2 ^ (prefixWord ++ tailWord_77775).sum := by decide
  have hdescent : baseEnd_77775 < baseStart_77775 := by decide
  rcases family_descends (prefixWord ++ tailWord_77775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77832 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_77832 : Nat := 118140960795 + 77832 * 2 ^ 59
def prefixEnd_77832 : Nat := 4983230072969 + 3 ^ 40 * 77832 * 2
def baseEnd_77832 : Nat := 39965226300844715642063

theorem tailTrace_77832 : CollatzResearch.WordTrace tailWord_77832 prefixEnd_77832 39965226300844715642063 := by
  unfold tailWord_77832
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419383127017715746213875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1892510836023620994951833 1419383127017715746213875)
  ·
    refine ⟨2129074690526573619320813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1419383127017715746213875 2129074690526573619320813)
    ·
      refine ⟨798403008947465107245305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2129074690526573619320813 798403008947465107245305)
      ·
        refine ⟨598802256710598830433979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 798403008947465107245305 598802256710598830433979)
        ·
          refine ⟨898203385065898245650969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598802256710598830433979 898203385065898245650969)
          ·
            refine ⟨673652538799423684238227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898203385065898245650969 673652538799423684238227)
            ·
              refine ⟨1010478808199135526357341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673652538799423684238227 1010478808199135526357341)
              ·
                refine ⟨378929553074675822384003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1010478808199135526357341 378929553074675822384003)
                ·
                  refine ⟨568394329612013733576005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378929553074675822384003 568394329612013733576005)
                  ·
                    refine ⟨106573936802252575045501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568394329612013733576005 106573936802252575045501)
                    ·
                      refine ⟨39965226300844715642063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106573936802252575045501 39965226300844715642063)
                      ·
                        rfl

theorem cell23_77832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_77832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77832 prefixEnd_77832 := by exact prefixLift 77832
  have htrace : WordTrace (prefixWord ++ tailWord_77832) baseStart_77832 baseEnd_77832 := by
    simpa [prefixWord, tailWord_77832, baseEnd_77832] using wordTrace_append hprefix tailTrace_77832
  have hstable : (prefixWord ++ tailWord_77832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77832).length < 2 ^ (prefixWord ++ tailWord_77832).sum := by decide
  have hdescent : baseEnd_77832 < baseStart_77832 := by decide
  rcases family_descends (prefixWord ++ tailWord_77832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77835 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 10]
def baseStart_77835 : Nat := 118140960795 + 77835 * 2 ^ 59
def prefixEnd_77835 : Nat := 4983230072969 + 3 ^ 40 * 77835 * 2
def baseEnd_77835 : Nat := 4440751860312022656061

theorem tailTrace_77835 : CollatzResearch.WordTrace tailWord_77835 prefixEnd_77835 4440751860312022656061 := by
  unfold tailWord_77835
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838875673024563004786959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1892583782016375336524639 2838875673024563004786959)
  ·
    refine ⟨4258313509536844507180439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2838875673024563004786959 4258313509536844507180439)
    ·
      refine ⟨6387470264305266760770659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4258313509536844507180439 6387470264305266760770659)
      ·
        refine ⟨9581205396457900141155989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6387470264305266760770659 9581205396457900141155989)
        ·
          refine ⟨449119002958964069116687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9581205396457900141155989 449119002958964069116687)
          ·
            refine ⟨673678504438446103675031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449119002958964069116687 673678504438446103675031)
            ·
              refine ⟨1010517756657669155512547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673678504438446103675031 1010517756657669155512547)
              ·
                refine ⟨1515776634986503733268821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010517756657669155512547 1515776634986503733268821)
                ·
                  refine ⟨4440751860312022656061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1515776634986503733268821 4440751860312022656061)
                  ·
                    rfl

theorem cell23_77835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 10].length) (baseStart_77835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77835 prefixEnd_77835 := by exact prefixLift 77835
  have htrace : WordTrace (prefixWord ++ tailWord_77835) baseStart_77835 baseEnd_77835 := by
    simpa [prefixWord, tailWord_77835, baseEnd_77835] using wordTrace_append hprefix tailTrace_77835
  have hstable : (prefixWord ++ tailWord_77835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77835).length < 2 ^ (prefixWord ++ tailWord_77835).sum := by decide
  have hdescent : baseEnd_77835 < baseStart_77835 := by decide
  rcases family_descends (prefixWord ++ tailWord_77835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77852 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 8]
def baseStart_77852 : Nat := 118140960795 + 77852 * 2 ^ 59
def prefixEnd_77852 : Nat := 4983230072969 + 3 ^ 40 * 77852 * 2
def baseEnd_77852 : Nat := 4441721768214959710219

theorem tailTrace_77852 : CollatzResearch.WordTrace tailWord_77852 prefixEnd_77852 4441721768214959710219 := by
  unfold tailWord_77852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419747856981487454077905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1892997142641983272103873 1419747856981487454077905)
  ·
    refine ⟨1064810892736115590558429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1419747856981487454077905 1064810892736115590558429)
    ·
      refine ⟨399304084776043346459411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1064810892736115590558429 399304084776043346459411)
      ·
        refine ⟨598956127164065019689117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399304084776043346459411 598956127164065019689117)
        ·
          refine ⟨224608547686524382383419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 598956127164065019689117 224608547686524382383419)
          ·
            refine ⟨336912821529786573575129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224608547686524382383419 336912821529786573575129)
            ·
              refine ⟨252684616147339930181347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336912821529786573575129 252684616147339930181347)
              ·
                refine ⟨379026924221009895272021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252684616147339930181347 379026924221009895272021)
                ·
                  refine ⟨4441721768214959710219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 379026924221009895272021 4441721768214959710219)
                  ·
                    rfl

theorem cell23_77852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_77852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77852 prefixEnd_77852 := by exact prefixLift 77852
  have htrace : WordTrace (prefixWord ++ tailWord_77852) baseStart_77852 baseEnd_77852 := by
    simpa [prefixWord, tailWord_77852, baseEnd_77852] using wordTrace_append hprefix tailTrace_77852
  have hstable : (prefixWord ++ tailWord_77852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77852).length < 2 ^ (prefixWord ++ tailWord_77852).sum := by decide
  have hdescent : baseEnd_77852 < baseStart_77852 := by decide
  rcases family_descends (prefixWord ++ tailWord_77852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77879 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_77879 : Nat := 118140960795 + 77879 * 2 ^ 59
def prefixEnd_77879 : Nat := 4983230072969 + 3 ^ 40 * 77879 * 2
def baseEnd_77879 : Nat := 39989359891606031754347

theorem tailTrace_77879 : CollatzResearch.WordTrace tailWord_77879 prefixEnd_77879 39989359891606031754347 := by
  unfold tailWord_77879
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840480484865158519388691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1893653656576772346259127 2840480484865158519388691)
  ·
    refine ⟨4260720727297737779083037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2840480484865158519388691 4260720727297737779083037)
    ·
      refine ⟨1597770272736651667156139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4260720727297737779083037 1597770272736651667156139)
      ·
        refine ⟨2396655409104977500734209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597770272736651667156139 2396655409104977500734209)
        ·
          refine ⟨1797491556828733125550657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2396655409104977500734209 1797491556828733125550657)
          ·
            refine ⟨1348118667621549844162993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797491556828733125550657 1348118667621549844162993)
            ·
              refine ⟨1011089000716162383122245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348118667621549844162993 1011089000716162383122245)
              ·
                refine ⟨189579187634280446835421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1011089000716162383122245 189579187634280446835421)
                ·
                  refine ⟨71092195362855167563283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189579187634280446835421 71092195362855167563283)
                  ·
                    refine ⟨106638293044282751344925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71092195362855167563283 106638293044282751344925)
                    ·
                      refine ⟨39989359891606031754347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106638293044282751344925 39989359891606031754347)
                      ·
                        rfl

theorem cell23_77879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_77879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77879 prefixEnd_77879 := by exact prefixLift 77879
  have htrace : WordTrace (prefixWord ++ tailWord_77879) baseStart_77879 baseEnd_77879 := by
    simpa [prefixWord, tailWord_77879, baseEnd_77879] using wordTrace_append hprefix tailTrace_77879
  have hstable : (prefixWord ++ tailWord_77879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77879).length < 2 ^ (prefixWord ++ tailWord_77879).sum := by decide
  have hdescent : baseEnd_77879 < baseStart_77879 := by decide
  rcases family_descends (prefixWord ++ tailWord_77879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77929 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 2, 4]
def baseStart_77929 : Nat := 118140960795 + 77929 * 2 ^ 59
def prefixEnd_77929 : Nat := 4983230072969 + 3 ^ 40 * 77929 * 2
def baseEnd_77929 : Nat := 13338344641443612043039

theorem tailTrace_77929 : CollatzResearch.WordTrace tailWord_77929 prefixEnd_77929 13338344641443612043039 := by
  unfold tailWord_77929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842304134684017058708841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1894869423122678039139227 2842304134684017058708841)
  ·
    refine ⟨2131728101013012794031631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2842304134684017058708841 2131728101013012794031631)
    ·
      refine ⟨3197592151519519191047447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131728101013012794031631 3197592151519519191047447)
      ·
        refine ⟨4796388227279278786571171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197592151519519191047447 4796388227279278786571171)
        ·
          refine ⟨7194582340918918179856757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4796388227279278786571171 7194582340918918179856757)
          ·
            refine ⟨674492094461148579361571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7194582340918918179856757 674492094461148579361571)
            ·
              refine ⟨1011738141691722869042357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674492094461148579361571 1011738141691722869042357)
              ·
                refine ⟨94850450783599018972721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011738141691722869042357 94850450783599018972721)
                ·
                  refine ⟨71137838087699264229541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94850450783599018972721 71137838087699264229541)
                  ·
                    refine ⟨13338344641443612043039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71137838087699264229541 13338344641443612043039)
                    ·
                      rfl

theorem cell23_77929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_77929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77929 prefixEnd_77929 := by exact prefixLift 77929
  have htrace : WordTrace (prefixWord ++ tailWord_77929) baseStart_77929 baseEnd_77929 := by
    simpa [prefixWord, tailWord_77929, baseEnd_77929] using wordTrace_append hprefix tailTrace_77929
  have hstable : (prefixWord ++ tailWord_77929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77929).length < 2 ^ (prefixWord ++ tailWord_77929).sum := by decide
  have hdescent : baseEnd_77929 < baseStart_77929 := by decide
  rcases family_descends (prefixWord ++ tailWord_77929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77936 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 5, 2, 2]
def baseStart_77936 : Nat := 118140960795 + 77936 * 2 ^ 59
def prefixEnd_77936 : Nat := 4983230072969 + 3 ^ 40 * 77936 * 2
def baseEnd_77936 : Nat := 40018628288912308741585

theorem tailTrace_77936 : CollatzResearch.WordTrace tailWord_77936 prefixEnd_77936 40018628288912308741585 := by
  unfold tailWord_77936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421279722829328627106831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1895039630439104836142441 1421279722829328627106831)
  ·
    refine ⟨2131919584243992940660247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421279722829328627106831 2131919584243992940660247)
    ·
      refine ⟨3197879376365989410990371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131919584243992940660247 3197879376365989410990371)
      ·
        refine ⟨4796819064548984116485557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197879376365989410990371 4796819064548984116485557)
        ·
          refine ⟨449701787301467260920521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4796819064548984116485557 449701787301467260920521)
          ·
            refine ⟨337276340476100445690391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449701787301467260920521 337276340476100445690391)
            ·
              refine ⟨505914510714150668535587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337276340476100445690391 505914510714150668535587)
              ·
                refine ⟨758871766071226002803381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505914510714150668535587 758871766071226002803381)
                ·
                  refine ⟨71144228069177437762817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 758871766071226002803381 71144228069177437762817)
                  ·
                    refine ⟨53358171051883078322113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71144228069177437762817 53358171051883078322113)
                    ·
                      refine ⟨40018628288912308741585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53358171051883078322113 40018628288912308741585)
                      ·
                        rfl

theorem cell23_77936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 2, 2].length) (baseStart_77936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77936 prefixEnd_77936 := by exact prefixLift 77936
  have htrace : WordTrace (prefixWord ++ tailWord_77936) baseStart_77936 baseEnd_77936 := by
    simpa [prefixWord, tailWord_77936, baseEnd_77936] using wordTrace_append hprefix tailTrace_77936
  have hstable : (prefixWord ++ tailWord_77936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77936).length < 2 ^ (prefixWord ++ tailWord_77936).sum := by decide
  have hdescent : baseEnd_77936 < baseStart_77936 := by decide
  rcases family_descends (prefixWord ++ tailWord_77936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77949 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_77949 : Nat := 118140960795 + 77949 * 2 ^ 59
def prefixEnd_77949 : Nat := 4983230072969 + 3 ^ 40 * 77949 * 2
def baseEnd_77949 : Nat := 40025303537420757879025

theorem tailTrace_77949 : CollatzResearch.WordTrace tailWord_77949 prefixEnd_77949 40025303537420757879025 := by
  unfold tailWord_77949
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843033594611560474436901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1895355729741040316291267 2843033594611560474436901)
  ·
    refine ⟨533068798989667588956919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2843033594611560474436901 533068798989667588956919)
    ·
      refine ⟨799603198484501383435379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533068798989667588956919 799603198484501383435379)
      ·
        refine ⟨1199404797726752075153069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799603198484501383435379 1199404797726752075153069)
        ·
          refine ⟨449776799147532028182401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1199404797726752075153069 449776799147532028182401)
          ·
            refine ⟨337332599360649021136801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449776799147532028182401 337332599360649021136801)
            ·
              refine ⟨252999449520486765852601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337332599360649021136801 252999449520486765852601)
              ·
                refine ⟨189749587140365074389451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252999449520486765852601 189749587140365074389451)
                ·
                  refine ⟨284624380710547611584177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189749587140365074389451 284624380710547611584177)
                  ·
                    refine ⟨213468285532910708688133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284624380710547611584177 213468285532910708688133)
                    ·
                      refine ⟨40025303537420757879025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 213468285532910708688133 40025303537420757879025)
                      ·
                        rfl

theorem cell23_77949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_77949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77949 prefixEnd_77949 := by exact prefixLift 77949
  have htrace : WordTrace (prefixWord ++ tailWord_77949) baseStart_77949 baseEnd_77949 := by
    simpa [prefixWord, tailWord_77949, baseEnd_77949] using wordTrace_append hprefix tailTrace_77949
  have hstable : (prefixWord ++ tailWord_77949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77949).length < 2 ^ (prefixWord ++ tailWord_77949).sum := by decide
  have hdescent : baseEnd_77949 < baseStart_77949 := by decide
  rcases family_descends (prefixWord ++ tailWord_77949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77956 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_77956 : Nat := 118140960795 + 77956 * 2 ^ 59
def prefixEnd_77956 : Nat := 4983230072969 + 3 ^ 40 * 77956 * 2
def baseEnd_77956 : Nat := 40028897902002230491493

theorem tailTrace_77956 : CollatzResearch.WordTrace tailWord_77956 prefixEnd_77956 40028897902002230491493 := by
  unfold tailWord_77956
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421644452793100334970861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1895525937057467113294481 1421644452793100334970861)
  ·
    refine ⟨533116669797412625614073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1421644452793100334970861 533116669797412625614073)
    ·
      refine ⟨399837502348059469210555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 533116669797412625614073 399837502348059469210555)
      ·
        refine ⟨599756253522089203815833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399837502348059469210555 599756253522089203815833)
        ·
          refine ⟨449817190141566902861875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599756253522089203815833 449817190141566902861875)
          ·
            refine ⟨674725785212350354292813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449817190141566902861875 674725785212350354292813)
            ·
              refine ⟨253022169454631382859805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 674725785212350354292813 253022169454631382859805)
              ·
                refine ⟨94883313545486768572427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253022169454631382859805 94883313545486768572427)
                ·
                  refine ⟨142324970318230152858641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94883313545486768572427 142324970318230152858641)
                  ·
                    refine ⟨106743727738672614643981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142324970318230152858641 106743727738672614643981)
                    ·
                      refine ⟨40028897902002230491493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106743727738672614643981 40028897902002230491493)
                      ·
                        rfl

theorem cell23_77956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_77956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77956 prefixEnd_77956 := by exact prefixLift 77956
  have htrace : WordTrace (prefixWord ++ tailWord_77956) baseStart_77956 baseEnd_77956 := by
    simpa [prefixWord, tailWord_77956, baseEnd_77956] using wordTrace_append hprefix tailTrace_77956
  have hstable : (prefixWord ++ tailWord_77956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77956).length < 2 ^ (prefixWord ++ tailWord_77956).sum := by decide
  have hdescent : baseEnd_77956 < baseStart_77956 := by decide
  rcases family_descends (prefixWord ++ tailWord_77956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77970 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_77970 : Nat := 118140960795 + 77970 * 2 ^ 59
def prefixEnd_77970 : Nat := 4983230072969 + 3 ^ 40 * 77970 * 2
def baseEnd_77970 : Nat := 40036086631165175716429

theorem tailTrace_77970 : CollatzResearch.WordTrace tailWord_77970 prefixEnd_77970 40036086631165175716429 := by
  unfold tailWord_77970
  simp only [CollatzResearch.WordTrace]
  refine ⟨710949881883870265237841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1895866351690320707300909 710949881883870265237841)
  ·
    refine ⟨533212411412902698928381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 710949881883870265237841 533212411412902698928381)
    ·
      refine ⟨199954654279838512098143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 533212411412902698928381 199954654279838512098143)
      ·
        refine ⟨299931981419757768147215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199954654279838512098143 299931981419757768147215)
        ·
          refine ⟨449897972129636652220823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299931981419757768147215 449897972129636652220823)
          ·
            refine ⟨674846958194454978331235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449897972129636652220823 674846958194454978331235)
            ·
              refine ⟨1012270437291682467496853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674846958194454978331235 1012270437291682467496853)
              ·
                refine ⟨47450176748047615663915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1012270437291682467496853 47450176748047615663915)
                ·
                  refine ⟨71175265122071423495873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47450176748047615663915 71175265122071423495873)
                  ·
                    refine ⟨53381448841553567621905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71175265122071423495873 53381448841553567621905)
                    ·
                      refine ⟨40036086631165175716429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53381448841553567621905 40036086631165175716429)
                      ·
                        rfl

theorem cell23_77970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_77970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_77970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_77970 prefixEnd_77970 := by exact prefixLift 77970
  have htrace : WordTrace (prefixWord ++ tailWord_77970) baseStart_77970 baseEnd_77970 := by
    simpa [prefixWord, tailWord_77970, baseEnd_77970] using wordTrace_append hprefix tailTrace_77970
  have hstable : (prefixWord ++ tailWord_77970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77970).length < 2 ^ (prefixWord ++ tailWord_77970).sum := by decide
  have hdescent : baseEnd_77970 < baseStart_77970 := by decide
  rcases family_descends (prefixWord ++ tailWord_77970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78037 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 2, 1, 3]
def baseStart_78037 : Nat := 118140960795 + 78037 * 2 ^ 59
def prefixEnd_78037 : Nat := 4983230072969 + 3 ^ 40 * 78037 * 2
def baseEnd_78037 : Nat := 40070489835016413578621

theorem tailTrace_78037 : CollatzResearch.WordTrace tailWord_78037 prefixEnd_78037 40070489835016413578621 := by
  unfold tailWord_78037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846243218292751503640365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1897495478861834335760243 2846243218292751503640365)
  ·
    refine ⟨1067341206859781813865137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2846243218292751503640365 1067341206859781813865137)
    ·
      refine ⟨800505905144836360398853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1067341206859781813865137 800505905144836360398853)
      ·
        refine ⟨150094857214656817574785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 800505905144836360398853 150094857214656817574785)
        ·
          refine ⟨112571142910992613181089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150094857214656817574785 112571142910992613181089)
          ·
            refine ⟨84428357183244459885817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112571142910992613181089 84428357183244459885817)
            ·
              refine ⟨63321267887433344914363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84428357183244459885817 63321267887433344914363)
              ·
                refine ⟨94981901831150017371545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63321267887433344914363 94981901831150017371545)
                ·
                  refine ⟨71236426373362513028659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94981901831150017371545 71236426373362513028659)
                  ·
                    refine ⟨106854639560043769542989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71236426373362513028659 106854639560043769542989)
                    ·
                      refine ⟨40070489835016413578621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106854639560043769542989 40070489835016413578621)
                      ·
                        rfl

theorem cell23_78037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_78037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78037 prefixEnd_78037 := by exact prefixLift 78037
  have htrace : WordTrace (prefixWord ++ tailWord_78037) baseStart_78037 baseEnd_78037 := by
    simpa [prefixWord, tailWord_78037, baseEnd_78037] using wordTrace_append hprefix tailTrace_78037
  have hstable : (prefixWord ++ tailWord_78037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78037).length < 2 ^ (prefixWord ++ tailWord_78037).sum := by decide
  have hdescent : baseEnd_78037 < baseStart_78037 := by decide
  rcases family_descends (prefixWord ++ tailWord_78037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78079 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 2, 5]
def baseStart_78079 : Nat := 118140960795 + 78079 * 2 ^ 59
def prefixEnd_78079 : Nat := 4983230072969 + 3 ^ 40 * 78079 * 2
def baseEnd_78079 : Nat := 13364018674168416417809

theorem tailTrace_78079 : CollatzResearch.WordTrace tailWord_78079 prefixEnd_78079 13364018674168416417809 := by
  unfold tailWord_78079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847775084140592676669291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1898516722760395117779527 2847775084140592676669291)
  ·
    refine ⟨4271662626210889015003937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847775084140592676669291 4271662626210889015003937)
    ·
      refine ⟨3203746969658166761252953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4271662626210889015003937 3203746969658166761252953)
      ·
        refine ⟨2402810227243625070939715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3203746969658166761252953 2402810227243625070939715)
        ·
          refine ⟨3604215340865437606409573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402810227243625070939715 3604215340865437606409573)
          ·
            refine ⟨675790376412269551201795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3604215340865437606409573 675790376412269551201795)
            ·
              refine ⟨1013685564618404326802693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675790376412269551201795 1013685564618404326802693)
              ·
                refine ⟨190066043365950811275505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1013685564618404326802693 190066043365950811275505)
                ·
                  refine ⟨142549532524463108456629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190066043365950811275505 142549532524463108456629)
                  ·
                    refine ⟨13364018674168416417809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142549532524463108456629 13364018674168416417809)
                    ·
                      rfl

theorem cell23_78079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_78079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78079 prefixEnd_78079 := by exact prefixLift 78079
  have htrace : WordTrace (prefixWord ++ tailWord_78079) baseStart_78079 baseEnd_78079 := by
    simpa [prefixWord, tailWord_78079, baseEnd_78079] using wordTrace_append hprefix tailTrace_78079
  have hstable : (prefixWord ++ tailWord_78079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78079).length < 2 ^ (prefixWord ++ tailWord_78079).sum := by decide
  have hdescent : baseEnd_78079 < baseStart_78079 := by decide
  rcases family_descends (prefixWord ++ tailWord_78079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78089 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_78089 : Nat := 118140960795 + 78089 * 2 ^ 59
def prefixEnd_78089 : Nat := 4983230072969 + 3 ^ 40 * 78089 * 2
def baseEnd_78089 : Nat := 40097190829050210128381

theorem tailTrace_78089 : CollatzResearch.WordTrace tailWord_78089 prefixEnd_78089 40097190829050210128381 := by
  unfold tailWord_78089
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848139814104364384533321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1898759876069576256355547 2848139814104364384533321)
  ·
    refine ⟨2136104860578273288399991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2848139814104364384533321 2136104860578273288399991)
    ·
      refine ⟨3204157290867409932599987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136104860578273288399991 3204157290867409932599987)
      ·
        refine ⟨4806235936301114898899981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204157290867409932599987 4806235936301114898899981)
        ·
          refine ⟨1802338476112918087087493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4806235936301114898899981 1802338476112918087087493)
          ·
            refine ⟨337938464271172141328905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1802338476112918087087493 337938464271172141328905)
            ·
              refine ⟨253453848203379105996679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337938464271172141328905 253453848203379105996679)
              ·
                refine ⟨380180772305068658995019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253453848203379105996679 380180772305068658995019)
                ·
                  refine ⟨570271158457602988492529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380180772305068658995019 570271158457602988492529)
                  ·
                    refine ⟨427703368843202241369397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570271158457602988492529 427703368843202241369397)
                    ·
                      refine ⟨40097190829050210128381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 427703368843202241369397 40097190829050210128381)
                      ·
                        rfl

theorem cell23_78089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_78089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78089 prefixEnd_78089 := by exact prefixLift 78089
  have htrace : WordTrace (prefixWord ++ tailWord_78089) baseStart_78089 baseEnd_78089 := by
    simpa [prefixWord, tailWord_78089, baseEnd_78089] using wordTrace_append hprefix tailTrace_78089
  have hstable : (prefixWord ++ tailWord_78089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78089).length < 2 ^ (prefixWord ++ tailWord_78089).sum := by decide
  have hdescent : baseEnd_78089 < baseStart_78089 := by decide
  rcases family_descends (prefixWord ++ tailWord_78089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78099 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 4]
def baseStart_78099 : Nat := 118140960795 + 78099 * 2 ^ 59
def prefixEnd_78099 : Nat := 4983230072969 + 3 ^ 40 * 78099 * 2
def baseEnd_78099 : Nat := 40102325635595171003335

theorem tailTrace_78099 : CollatzResearch.WordTrace tailWord_78099 prefixEnd_78099 40102325635595171003335 := by
  unfold tailWord_78099
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848504544068136092397351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1899003029378757394931567 2848504544068136092397351)
  ·
    refine ⟨4272756816102204138596027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848504544068136092397351 4272756816102204138596027)
    ·
      refine ⟨6409135224153306207894041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272756816102204138596027 6409135224153306207894041)
      ·
        refine ⟨4806851418114979655920531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6409135224153306207894041 4806851418114979655920531)
        ·
          refine ⟨7210277127172469483880797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806851418114979655920531 7210277127172469483880797)
          ·
            refine ⟨2703853922689676056455299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7210277127172469483880797 2703853922689676056455299)
            ·
              refine ⟨4055780884034514084682949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703853922689676056455299 4055780884034514084682949)
              ·
                refine ⟨760458915756471390878053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4055780884034514084682949 760458915756471390878053)
                ·
                  refine ⟨142586046704338385789635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760458915756471390878053 142586046704338385789635)
                  ·
                    refine ⟨213879070056507578684453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142586046704338385789635 213879070056507578684453)
                    ·
                      refine ⟨40102325635595171003335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 213879070056507578684453 40102325635595171003335)
                      ·
                        rfl

theorem cell23_78099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_78099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78099 prefixEnd_78099 := by exact prefixLift 78099
  have htrace : WordTrace (prefixWord ++ tailWord_78099) baseStart_78099 baseEnd_78099 := by
    simpa [prefixWord, tailWord_78099, baseEnd_78099] using wordTrace_append hprefix tailTrace_78099
  have hstable : (prefixWord ++ tailWord_78099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78099).length < 2 ^ (prefixWord ++ tailWord_78099).sum := by decide
  have hdescent : baseEnd_78099 < baseStart_78099 := by decide
  rcases family_descends (prefixWord ++ tailWord_78099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78116 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_78116 : Nat := 118140960795 + 78116 * 2 ^ 59
def prefixEnd_78116 : Nat := 4983230072969 + 3 ^ 40 * 78116 * 2
def baseEnd_78116 : Nat := 40111054806721604490757

theorem tailTrace_78116 : CollatzResearch.WordTrace tailWord_78116 prefixEnd_78116 40111054806721604490757 := by
  unfold tailWord_78116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424562292503273997883101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1899416390004365330510801 1424562292503273997883101)
  ·
    refine ⟨534210859688727749206163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1424562292503273997883101 534210859688727749206163)
    ·
      refine ⟨801316289533091623809245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534210859688727749206163 801316289533091623809245)
      ·
        refine ⟨300493608574909358928467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 801316289533091623809245 300493608574909358928467)
        ·
          refine ⟨450740412862364038392701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300493608574909358928467 450740412862364038392701)
          ·
            refine ⟨169027654823386514397263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450740412862364038392701 169027654823386514397263)
            ·
              refine ⟨253541482235079771595895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169027654823386514397263 253541482235079771595895)
              ·
                refine ⟨380312223352619657393843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253541482235079771595895 380312223352619657393843)
                ·
                  refine ⟨570468335028929486090765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380312223352619657393843 570468335028929486090765)
                  ·
                    refine ⟨213925625635848557284037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 570468335028929486090765 213925625635848557284037)
                    ·
                      refine ⟨40111054806721604490757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 213925625635848557284037 40111054806721604490757)
                      ·
                        rfl

theorem cell23_78116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_78116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78116 prefixEnd_78116 := by exact prefixLift 78116
  have htrace : WordTrace (prefixWord ++ tailWord_78116) baseStart_78116 baseEnd_78116 := by
    simpa [prefixWord, tailWord_78116, baseEnd_78116] using wordTrace_append hprefix tailTrace_78116
  have hstable : (prefixWord ++ tailWord_78116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78116).length < 2 ^ (prefixWord ++ tailWord_78116).sum := by decide
  have hdescent : baseEnd_78116 < baseStart_78116 := by decide
  rcases family_descends (prefixWord ++ tailWord_78116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78136 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_78136 : Nat := 118140960795 + 78136 * 2 ^ 59
def prefixEnd_78136 : Nat := 4983230072969 + 3 ^ 40 * 78136 * 2
def baseEnd_78136 : Nat := 40121324419811526240665

theorem tailTrace_78136 : CollatzResearch.WordTrace tailWord_78136 prefixEnd_78136 40121324419811526240665 := by
  unfold tailWord_78136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424927022467045705747131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1899902696622727607662841 1424927022467045705747131)
  ·
    refine ⟨2137390533700568558620697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424927022467045705747131 2137390533700568558620697)
    ·
      refine ⟨1603042900275426418965523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2137390533700568558620697 1603042900275426418965523)
      ·
        refine ⟨2404564350413139628448285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603042900275426418965523 2404564350413139628448285)
        ·
          refine ⟨901711631404927360668107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2404564350413139628448285 901711631404927360668107)
          ·
            refine ⟨1352567447107391041002161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901711631404927360668107 1352567447107391041002161)
            ·
              refine ⟨1014425585330543280751621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352567447107391041002161 1014425585330543280751621)
              ·
                refine ⟨190204797249476865140929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1014425585330543280751621 190204797249476865140929)
                ·
                  refine ⟨142653597937107648855697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190204797249476865140929 142653597937107648855697)
                  ·
                    refine ⟨106990198452830736641773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142653597937107648855697 106990198452830736641773)
                    ·
                      refine ⟨40121324419811526240665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 106990198452830736641773 40121324419811526240665)
                      ·
                        rfl

theorem cell23_78136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_78136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78136 prefixEnd_78136 := by exact prefixLift 78136
  have htrace : WordTrace (prefixWord ++ tailWord_78136) baseStart_78136 baseEnd_78136 := by
    simpa [prefixWord, tailWord_78136, baseEnd_78136] using wordTrace_append hprefix tailTrace_78136
  have hstable : (prefixWord ++ tailWord_78136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78136).length < 2 ^ (prefixWord ++ tailWord_78136).sum := by decide
  have hdescent : baseEnd_78136 < baseStart_78136 := by decide
  rcases family_descends (prefixWord ++ tailWord_78136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78143 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 1, 4]
def baseStart_78143 : Nat := 118140960795 + 78143 * 2 ^ 59
def prefixEnd_78143 : Nat := 4983230072969 + 3 ^ 40 * 78143 * 2
def baseEnd_78143 : Nat := 13374972928130999617711

theorem tailTrace_78143 : CollatzResearch.WordTrace tailWord_78143 prefixEnd_78143 13374972928130999617711 := by
  unfold tailWord_78143
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850109355908731606999083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1900072903939154404666055 2850109355908731606999083)
  ·
    refine ⟨4275164033863097410498625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2850109355908731606999083 4275164033863097410498625)
    ·
      refine ⟨3206373025397323057873969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4275164033863097410498625 3206373025397323057873969)
      ·
        refine ⟨2404779769047992293405477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3206373025397323057873969 2404779769047992293405477)
        ·
          refine ⟨450896206696498555013527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2404779769047992293405477 450896206696498555013527)
          ·
            refine ⟨676344310044747832520291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450896206696498555013527 676344310044747832520291)
            ·
              refine ⟨1014516465067121748780437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676344310044747832520291 1014516465067121748780437)
              ·
                refine ⟨47555459300021331974083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1014516465067121748780437 47555459300021331974083)
                ·
                  refine ⟨71333188950031997961125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47555459300021331974083 71333188950031997961125)
                  ·
                    refine ⟨13374972928130999617711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71333188950031997961125 13374972928130999617711)
                    ·
                      rfl

theorem cell23_78143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 4].length) (baseStart_78143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78143 prefixEnd_78143 := by exact prefixLift 78143
  have htrace : WordTrace (prefixWord ++ tailWord_78143) baseStart_78143 baseEnd_78143 := by
    simpa [prefixWord, tailWord_78143, baseEnd_78143] using wordTrace_append hprefix tailTrace_78143
  have hstable : (prefixWord ++ tailWord_78143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78143).length < 2 ^ (prefixWord ++ tailWord_78143).sum := by decide
  have hdescent : baseEnd_78143 < baseStart_78143 := by decide
  rcases family_descends (prefixWord ++ tailWord_78143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78199 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 5, 6]
def baseStart_78199 : Nat := 118140960795 + 78199 * 2 ^ 59
def prefixEnd_78199 : Nat := 4983230072969 + 3 ^ 40 * 78199 * 2
def baseEnd_78199 : Nat := 13384557900348259917625

theorem tailTrace_78199 : CollatzResearch.WordTrace tailWord_78199 prefixEnd_78199 13384557900348259917625 := by
  unfold tailWord_78199
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852151843705853171037651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1901434562470568780691767 2852151843705853171037651)
  ·
    refine ⟨4278227765558779756556477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852151843705853171037651 4278227765558779756556477)
    ·
      refine ⟨1604335412084542408708679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4278227765558779756556477 1604335412084542408708679)
      ·
        refine ⟨2406503118126813613063019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604335412084542408708679 2406503118126813613063019)
        ·
          refine ⟨3609754677190220419594529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406503118126813613063019 3609754677190220419594529)
          ·
            refine ⟨2707316007892665314695897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3609754677190220419594529 2707316007892665314695897)
            ·
              refine ⟨2030487005919498986021923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707316007892665314695897 2030487005919498986021923)
              ·
                refine ⟨3045730508879248479032885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030487005919498986021923 3045730508879248479032885)
                ·
                  refine ⟨285537235207429544909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3045730508879248479032885 285537235207429544909333)
                  ·
                    refine ⟨13384557900348259917625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 285537235207429544909333 13384557900348259917625)
                    ·
                      rfl

theorem cell23_78199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_78199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78199 prefixEnd_78199 := by exact prefixLift 78199
  have htrace : WordTrace (prefixWord ++ tailWord_78199) baseStart_78199 baseEnd_78199 := by
    simpa [prefixWord, tailWord_78199, baseEnd_78199] using wordTrace_append hprefix tailTrace_78199
  have hstable : (prefixWord ++ tailWord_78199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78199).length < 2 ^ (prefixWord ++ tailWord_78199).sum := by decide
  have hdescent : baseEnd_78199 < baseStart_78199 := by decide
  rcases family_descends (prefixWord ++ tailWord_78199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78216 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_78216 : Nat := 118140960795 + 78216 * 2 ^ 59
def prefixEnd_78216 : Nat := 4983230072969 + 3 ^ 40 * 78216 * 2
def baseEnd_78216 : Nat := 13387467624057071080099

theorem tailTrace_78216 : CollatzResearch.WordTrace tailWord_78216 prefixEnd_78216 13387467624057071080099 := by
  unfold tailWord_78216
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426385942322132537203251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1901847923096176716271001 1426385942322132537203251)
  ·
    refine ⟨2139578913483198805804877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426385942322132537203251 2139578913483198805804877)
    ·
      refine ⟨802342092556199552176829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2139578913483198805804877 802342092556199552176829)
      ·
        refine ⟨300878284708574832066311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 802342092556199552176829 300878284708574832066311)
        ·
          refine ⟨451317427062862248099467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300878284708574832066311 451317427062862248099467)
          ·
            refine ⟨676976140594293372149201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451317427062862248099467 676976140594293372149201)
            ·
              refine ⟨507732105445720029111901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676976140594293372149201 507732105445720029111901)
              ·
                refine ⟨190399539542145010916963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507732105445720029111901 190399539542145010916963)
                ·
                  refine ⟨285599309313217516375445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190399539542145010916963 285599309313217516375445)
                  ·
                    refine ⟨13387467624057071080099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 285599309313217516375445 13387467624057071080099)
                    ·
                      rfl

theorem cell23_78216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_78216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78216 prefixEnd_78216 := by exact prefixLift 78216
  have htrace : WordTrace (prefixWord ++ tailWord_78216) baseStart_78216 baseEnd_78216 := by
    simpa [prefixWord, tailWord_78216, baseEnd_78216] using wordTrace_append hprefix tailTrace_78216
  have hstable : (prefixWord ++ tailWord_78216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78216).length < 2 ^ (prefixWord ++ tailWord_78216).sum := by decide
  have hdescent : baseEnd_78216 < baseStart_78216 := by decide
  rcases family_descends (prefixWord ++ tailWord_78216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78240 : List Nat := [2, 1, 1, 4, 1, 4, 3, 1, 1, 1, 4]
def baseStart_78240 : Nat := 118140960795 + 78240 * 2 ^ 59
def prefixEnd_78240 : Nat := 4983230072969 + 3 ^ 40 * 78240 * 2
def baseEnd_78240 : Nat := 40174726407879119340187

theorem tailTrace_78240 : CollatzResearch.WordTrace tailWord_78240 prefixEnd_78240 40174726407879119340187 := by
  unfold tailWord_78240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426823618278658586640087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1902431491038211448853449 1426823618278658586640087)
  ·
    refine ⟨2140235427417987879960131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426823618278658586640087 2140235427417987879960131)
    ·
      refine ⟨3210353141126981819940197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2140235427417987879960131 3210353141126981819940197)
      ·
        refine ⟨601941213961309091238787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3210353141126981819940197 601941213961309091238787)
        ·
          refine ⟨902911820941963636858181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601941213961309091238787 902911820941963636858181)
          ·
            refine ⟨169295966426618181910909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 902911820941963636858181 169295966426618181910909)
            ·
              refine ⟨63485987409981818216591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169295966426618181910909 63485987409981818216591)
              ·
                refine ⟨95228981114972727324887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63485987409981818216591 95228981114972727324887)
                ·
                  refine ⟨142843471672459090987331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95228981114972727324887 142843471672459090987331)
                  ·
                    refine ⟨214265207508688636480997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142843471672459090987331 214265207508688636480997)
                    ·
                      refine ⟨40174726407879119340187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 214265207508688636480997 40174726407879119340187)
                      ·
                        rfl

theorem cell23_78240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_78240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78240 prefixEnd_78240 := by exact prefixLift 78240
  have htrace : WordTrace (prefixWord ++ tailWord_78240) baseStart_78240 baseEnd_78240 := by
    simpa [prefixWord, tailWord_78240, baseEnd_78240] using wordTrace_append hprefix tailTrace_78240
  have hstable : (prefixWord ++ tailWord_78240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78240).length < 2 ^ (prefixWord ++ tailWord_78240).sum := by decide
  have hdescent : baseEnd_78240 < baseStart_78240 := by decide
  rcases family_descends (prefixWord ++ tailWord_78240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78243 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 5]
def baseStart_78243 : Nat := 118140960795 + 78243 * 2 ^ 59
def prefixEnd_78243 : Nat := 4983230072969 + 3 ^ 40 * 78243 * 2
def baseEnd_78243 : Nat := 40176266849842607602673

theorem tailTrace_78243 : CollatzResearch.WordTrace tailWord_78243 prefixEnd_78243 40176266849842607602673 := by
  unfold tailWord_78243
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853756655546448685639383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1902504437030965790426255 2853756655546448685639383)
  ·
    refine ⟨4280634983319673028459075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853756655546448685639383 4280634983319673028459075)
    ·
      refine ⟨6420952474979509542688613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280634983319673028459075 6420952474979509542688613)
      ·
        refine ⟨1203928589058658039254115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6420952474979509542688613 1203928589058658039254115)
        ·
          refine ⟨1805892883587987058881173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203928589058658039254115 1805892883587987058881173)
          ·
            refine ⟨84651228918186893385055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1805892883587987058881173 84651228918186893385055)
            ·
              refine ⟨126976843377280340077583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84651228918186893385055 126976843377280340077583)
              ·
                refine ⟨190465265065920510116375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126976843377280340077583 190465265065920510116375)
                ·
                  refine ⟨285697897598880765174563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190465265065920510116375 285697897598880765174563)
                  ·
                    refine ⟨428546846398321147761845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 285697897598880765174563 428546846398321147761845)
                    ·
                      refine ⟨40176266849842607602673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 428546846398321147761845 40176266849842607602673)
                      ·
                        rfl

theorem cell23_78243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_78243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78243 prefixEnd_78243 := by exact prefixLift 78243
  have htrace : WordTrace (prefixWord ++ tailWord_78243) baseStart_78243 baseEnd_78243 := by
    simpa [prefixWord, tailWord_78243, baseEnd_78243] using wordTrace_append hprefix tailTrace_78243
  have hstable : (prefixWord ++ tailWord_78243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78243).length < 2 ^ (prefixWord ++ tailWord_78243).sum := by decide
  have hdescent : baseEnd_78243 < baseStart_78243 := by decide
  rcases family_descends (prefixWord ++ tailWord_78243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78286 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_78286 : Nat := 118140960795 + 78286 * 2 ^ 59
def prefixEnd_78286 : Nat := 4983230072969 + 3 ^ 40 * 78286 * 2
def baseEnd_78286 : Nat := 40198346517985939364975

theorem tailTrace_78286 : CollatzResearch.WordTrace tailWord_78286 prefixEnd_78286 40198346517985939364975 := by
  unfold tailWord_78286
  simp only [CollatzResearch.WordTrace]
  refine ⟨356915624298833378681839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1903549996260444686303141 356915624298833378681839)
  ·
    refine ⟨535373436448250068022759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356915624298833378681839 535373436448250068022759)
    ·
      refine ⟨803060154672375102034139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535373436448250068022759 803060154672375102034139)
      ·
        refine ⟨1204590232008562653051209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803060154672375102034139 1204590232008562653051209)
        ·
          refine ⟨903442674006421989788407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204590232008562653051209 903442674006421989788407)
          ·
            refine ⟨1355164011009632984682611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903442674006421989788407 1355164011009632984682611)
            ·
              refine ⟨2032746016514449477023917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355164011009632984682611 2032746016514449477023917)
              ·
                refine ⟨762279756192918553883969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2032746016514449477023917 762279756192918553883969)
                ·
                  refine ⟨571709817144688915412977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762279756192918553883969 571709817144688915412977)
                  ·
                    refine ⟨428782362858516686559733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571709817144688915412977 428782362858516686559733)
                    ·
                      refine ⟨40198346517985939364975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 428782362858516686559733 40198346517985939364975)
                      ·
                        rfl

theorem cell23_78286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_78286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78286 prefixEnd_78286 := by exact prefixLift 78286
  have htrace : WordTrace (prefixWord ++ tailWord_78286) baseStart_78286 baseEnd_78286 := by
    simpa [prefixWord, tailWord_78286, baseEnd_78286] using wordTrace_append hprefix tailTrace_78286
  have hstable : (prefixWord ++ tailWord_78286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78286).length < 2 ^ (prefixWord ++ tailWord_78286).sum := by decide
  have hdescent : baseEnd_78286 < baseStart_78286 := by decide
  rcases family_descends (prefixWord ++ tailWord_78286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78353 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 5]
def baseStart_78353 : Nat := 118140960795 + 78353 * 2 ^ 59
def prefixEnd_78353 : Nat := 4983230072969 + 3 ^ 40 * 78353 * 2
def baseEnd_78353 : Nat := 4470305524648575247463

theorem tailTrace_78353 : CollatzResearch.WordTrace tailWord_78353 prefixEnd_78353 4470305524648575247463 := by
  unfold tailWord_78353
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857768685147937472143713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1905179123431958314762475 2857768685147937472143713)
  ·
    refine ⟨2143326513860953104107785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2857768685147937472143713 2143326513860953104107785)
    ·
      refine ⟨1607494885395714828080839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143326513860953104107785 1607494885395714828080839)
      ·
        refine ⟨2411242328093572242121259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607494885395714828080839 2411242328093572242121259)
        ·
          refine ⟨3616863492140358363181889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411242328093572242121259 3616863492140358363181889)
          ·
            refine ⟨2712647619105268772386417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3616863492140358363181889 2712647619105268772386417)
            ·
              refine ⟨2034485714328951579289813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712647619105268772386417 2034485714328951579289813)
              ·
                refine ⟨47683258929584802639605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2034485714328951579289813 47683258929584802639605)
                ·
                  refine ⟨4470305524648575247463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47683258929584802639605 4470305524648575247463)
                  ·
                    rfl

theorem cell23_78353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 5].length) (baseStart_78353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78353 prefixEnd_78353 := by exact prefixLift 78353
  have htrace : WordTrace (prefixWord ++ tailWord_78353) baseStart_78353 baseEnd_78353 := by
    simpa [prefixWord, tailWord_78353, baseEnd_78353] using wordTrace_append hprefix tailTrace_78353
  have hstable : (prefixWord ++ tailWord_78353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78353).length < 2 ^ (prefixWord ++ tailWord_78353).sum := by decide
  have hdescent : baseEnd_78353 < baseStart_78353 := by decide
  rcases family_descends (prefixWord ++ tailWord_78353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78420 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_78420 : Nat := 118140960795 + 78420 * 2 ^ 59
def prefixEnd_78420 : Nat := 4983230072969 + 3 ^ 40 * 78420 * 2
def baseEnd_78420 : Nat := 40267152925688415089359

theorem tailTrace_78420 : CollatzResearch.WordTrace tailWord_78420 prefixEnd_78420 40267152925688415089359 := by
  unfold tailWord_78420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430106187952603957416357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1906808250603471943221809 1430106187952603957416357)
  ·
    refine ⟨268144910241113242015567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1430106187952603957416357 268144910241113242015567)
    ·
      refine ⟨402217365361669863023351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268144910241113242015567 402217365361669863023351)
      ·
        refine ⟨603326048042504794535027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402217365361669863023351 603326048042504794535027)
        ·
          refine ⟨904989072063757191802541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603326048042504794535027 904989072063757191802541)
          ·
            refine ⟨339370902023908946925953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 904989072063757191802541 339370902023908946925953)
            ·
              refine ⟨254528176517931710194465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339370902023908946925953 254528176517931710194465)
              ·
                refine ⟨190896132388448782645849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254528176517931710194465 190896132388448782645849)
                ·
                  refine ⟨143172099291336586984387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190896132388448782645849 143172099291336586984387)
                  ·
                    refine ⟨214758148937004880476581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143172099291336586984387 214758148937004880476581)
                    ·
                      refine ⟨40267152925688415089359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 214758148937004880476581 40267152925688415089359)
                      ·
                        rfl

theorem cell23_78420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_78420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78420 prefixEnd_78420 := by exact prefixLift 78420
  have htrace : WordTrace (prefixWord ++ tailWord_78420) baseStart_78420 baseEnd_78420 := by
    simpa [prefixWord, tailWord_78420, baseEnd_78420] using wordTrace_append hprefix tailTrace_78420
  have hstable : (prefixWord ++ tailWord_78420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78420).length < 2 ^ (prefixWord ++ tailWord_78420).sum := by decide
  have hdescent : baseEnd_78420 < baseStart_78420 := by decide
  rcases family_descends (prefixWord ++ tailWord_78420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78437 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 2, 4, 2]
def baseStart_78437 : Nat := 118140960795 + 78437 * 2 ^ 59
def prefixEnd_78437 : Nat := 4983230072969 + 3 ^ 40 * 78437 * 2
def baseEnd_78437 : Nat := 40275882096814848576781

theorem tailTrace_78437 : CollatzResearch.WordTrace tailWord_78437 prefixEnd_78437 40275882096814848576781 := by
  unfold tailWord_78437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860832416843619818201565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1907221611229079878801043 2860832416843619818201565)
  ·
    refine ⟨1072812156316357431825587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2860832416843619818201565 1072812156316357431825587)
    ·
      refine ⟨1609218234474536147738381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1072812156316357431825587 1609218234474536147738381)
      ·
        refine ⟨603456837927951055401893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1609218234474536147738381 603456837927951055401893)
        ·
          refine ⟨113148157111490822887855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 603456837927951055401893 113148157111490822887855)
          ·
            refine ⟨169722235667236234331783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113148157111490822887855 169722235667236234331783)
            ·
              refine ⟨254583353500854351497675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169722235667236234331783 254583353500854351497675)
              ·
                refine ⟨381875030251281527246513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254583353500854351497675 381875030251281527246513)
                ·
                  refine ⟨286406272688461145434885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381875030251281527246513 286406272688461145434885)
                  ·
                    refine ⟨53701176129086464769041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286406272688461145434885 53701176129086464769041)
                    ·
                      refine ⟨40275882096814848576781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53701176129086464769041 40275882096814848576781)
                      ·
                        rfl

theorem cell23_78437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_78437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78437 prefixEnd_78437 := by exact prefixLift 78437
  have htrace : WordTrace (prefixWord ++ tailWord_78437) baseStart_78437 baseEnd_78437 := by
    simpa [prefixWord, tailWord_78437, baseEnd_78437] using wordTrace_append hprefix tailTrace_78437
  have hstable : (prefixWord ++ tailWord_78437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78437).length < 2 ^ (prefixWord ++ tailWord_78437).sum := by decide
  have hdescent : baseEnd_78437 < baseStart_78437 := by decide
  rcases family_descends (prefixWord ++ tailWord_78437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78454 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_78454 : Nat := 118140960795 + 78454 * 2 ^ 59
def prefixEnd_78454 : Nat := 4983230072969 + 3 ^ 40 * 78454 * 2
def baseEnd_78454 : Nat := 40284611267941282064203

theorem tailTrace_78454 : CollatzResearch.WordTrace tailWord_78454 prefixEnd_78454 40284611267941282064203 := by
  unfold tailWord_78454
  simp only [CollatzResearch.WordTrace]
  refine ⟨178840778611376982598151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1907634971854687814380277 178840778611376982598151)
  ·
    refine ⟨268261167917065473897227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178840778611376982598151 268261167917065473897227)
    ·
      refine ⟨402391751875598210845841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268261167917065473897227 402391751875598210845841)
      ·
        refine ⟨301793813906698658134381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402391751875598210845841 301793813906698658134381)
        ·
          refine ⟨113172680215011996800393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301793813906698658134381 113172680215011996800393)
          ·
            refine ⟨84879510161258997600295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113172680215011996800393 84879510161258997600295)
            ·
              refine ⟨127319265241888496400443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84879510161258997600295 127319265241888496400443)
              ·
                refine ⟨190978897862832744600665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127319265241888496400443 190978897862832744600665)
                ·
                  refine ⟨143234173397124558450499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190978897862832744600665 143234173397124558450499)
                  ·
                    refine ⟨214851260095686837675749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143234173397124558450499 214851260095686837675749)
                    ·
                      refine ⟨40284611267941282064203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 214851260095686837675749 40284611267941282064203)
                      ·
                        rfl

theorem cell23_78454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_78454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78454 prefixEnd_78454 := by exact prefixLift 78454
  have htrace : WordTrace (prefixWord ++ tailWord_78454) baseStart_78454 baseEnd_78454 := by
    simpa [prefixWord, tailWord_78454, baseEnd_78454] using wordTrace_append hprefix tailTrace_78454
  have hstable : (prefixWord ++ tailWord_78454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78454).length < 2 ^ (prefixWord ++ tailWord_78454).sum := by decide
  have hdescent : baseEnd_78454 < baseStart_78454 := by decide
  rcases family_descends (prefixWord ++ tailWord_78454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78457 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 3]
def baseStart_78457 : Nat := 118140960795 + 78457 * 2 ^ 59
def prefixEnd_78457 : Nat := 4983230072969 + 3 ^ 40 * 78457 * 2
def baseEnd_78457 : Nat := 40286151709904770326689

theorem tailTrace_78457 : CollatzResearch.WordTrace tailWord_78457 prefixEnd_78457 40286151709904770326689 := by
  unfold tailWord_78457
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861561876771163233929625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1907707917847442155953083 2861561876771163233929625)
  ·
    refine ⟨2146171407578372425447219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2861561876771163233929625 2146171407578372425447219)
    ·
      refine ⟨3219257111367558638170829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146171407578372425447219 3219257111367558638170829)
      ·
        refine ⟨1207221416762834489314061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3219257111367558638170829 1207221416762834489314061)
        ·
          refine ⟨452708031286062933492773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1207221416762834489314061 452708031286062933492773)
          ·
            refine ⟨84882755866136800029895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 452708031286062933492773 84882755866136800029895)
            ·
              refine ⟨127324133799205200044843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84882755866136800029895 127324133799205200044843)
              ·
                refine ⟨190986200698807800067265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127324133799205200044843 190986200698807800067265)
                ·
                  refine ⟨143239650524105850050449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190986200698807800067265 143239650524105850050449)
                  ·
                    refine ⟨107429737893079387537837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143239650524105850050449 107429737893079387537837)
                    ·
                      refine ⟨40286151709904770326689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 107429737893079387537837 40286151709904770326689)
                      ·
                        rfl

theorem cell23_78457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_78457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78457 prefixEnd_78457 := by exact prefixLift 78457
  have htrace : WordTrace (prefixWord ++ tailWord_78457) baseStart_78457 baseEnd_78457 := by
    simpa [prefixWord, tailWord_78457, baseEnd_78457] using wordTrace_append hprefix tailTrace_78457
  have hstable : (prefixWord ++ tailWord_78457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78457).length < 2 ^ (prefixWord ++ tailWord_78457).sum := by decide
  have hdescent : baseEnd_78457 < baseStart_78457 := by decide
  rcases family_descends (prefixWord ++ tailWord_78457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78487 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_78487 : Nat := 118140960795 + 78487 * 2 ^ 59
def prefixEnd_78487 : Nat := 4983230072969 + 3 ^ 40 * 78487 * 2
def baseEnd_78487 : Nat := 40301556129539652951551

theorem tailTrace_78487 : CollatzResearch.WordTrace tailWord_78487 prefixEnd_78487 40301556129539652951551 := by
  unfold tailWord_78487
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862656066662478357521715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1908437377774985571681143 2862656066662478357521715)
  ·
    refine ⟨4293984099993717536282573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2862656066662478357521715 4293984099993717536282573)
    ·
      refine ⟨1610244037497644076105965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4293984099993717536282573 1610244037497644076105965)
      ·
        refine ⟨603841514061616528539737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1610244037497644076105965 603841514061616528539737)
        ·
          refine ⟨452881135546212396404803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603841514061616528539737 452881135546212396404803)
          ·
            refine ⟨679321703319318594607205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452881135546212396404803 679321703319318594607205)
            ·
              refine ⟨127372819372372236488851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 679321703319318594607205 127372819372372236488851)
              ·
                refine ⟨191059229058558354733277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127372819372372236488851 191059229058558354733277)
                ·
                  refine ⟨71647210896959383024979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191059229058558354733277 71647210896959383024979)
                  ·
                    refine ⟨107470816345439074537469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71647210896959383024979 107470816345439074537469)
                    ·
                      refine ⟨40301556129539652951551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 107470816345439074537469 40301556129539652951551)
                      ·
                        rfl

theorem cell23_78487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_78487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78487 prefixEnd_78487 := by exact prefixLift 78487
  have htrace : WordTrace (prefixWord ++ tailWord_78487) baseStart_78487 baseEnd_78487 := by
    simpa [prefixWord, tailWord_78487, baseEnd_78487] using wordTrace_append hprefix tailTrace_78487
  have hstable : (prefixWord ++ tailWord_78487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78487).length < 2 ^ (prefixWord ++ tailWord_78487).sum := by decide
  have hdescent : baseEnd_78487 < baseStart_78487 := by decide
  rcases family_descends (prefixWord ++ tailWord_78487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78540 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_78540 : Nat := 118140960795 + 78540 * 2 ^ 59
def prefixEnd_78540 : Nat := 4983230072969 + 3 ^ 40 * 78540 * 2
def baseEnd_78540 : Nat := 40328770604227945588807

theorem tailTrace_78540 : CollatzResearch.WordTrace tailWord_78540 prefixEnd_78540 40328770604227945588807 := by
  unfold tailWord_78540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432294567735234204600537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1909726090313645606134049 1432294567735234204600537)
  ·
    refine ⟨1074220925801425653450403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1432294567735234204600537 1074220925801425653450403)
    ·
      refine ⟨1611331388702138480175605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074220925801425653450403 1611331388702138480175605)
      ·
        refine ⟨151062317690825482516463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1611331388702138480175605 151062317690825482516463)
        ·
          refine ⟨226593476536238223774695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151062317690825482516463 226593476536238223774695)
          ·
            refine ⟨339890214804357335662043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226593476536238223774695 339890214804357335662043)
            ·
              refine ⟨509835322206536003493065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339890214804357335662043 509835322206536003493065)
              ·
                refine ⟨382376491654902002619799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509835322206536003493065 382376491654902002619799)
                ·
                  refine ⟨573564737482353003929699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382376491654902002619799 573564737482353003929699)
                  ·
                    refine ⟨860347106223529505894549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 573564737482353003929699 860347106223529505894549)
                    ·
                      refine ⟨40328770604227945588807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 860347106223529505894549 40328770604227945588807)
                      ·
                        rfl

theorem cell23_78540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_78540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78540 prefixEnd_78540 := by exact prefixLift 78540
  have htrace : WordTrace (prefixWord ++ tailWord_78540) baseStart_78540 baseEnd_78540 := by
    simpa [prefixWord, tailWord_78540, baseEnd_78540] using wordTrace_append hprefix tailTrace_78540
  have hstable : (prefixWord ++ tailWord_78540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78540).length < 2 ^ (prefixWord ++ tailWord_78540).sum := by decide
  have hdescent : baseEnd_78540 < baseStart_78540 := by decide
  rcases family_descends (prefixWord ++ tailWord_78540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78553 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_78553 : Nat := 118140960795 + 78553 * 2 ^ 59
def prefixEnd_78553 : Nat := 4983230072969 + 3 ^ 40 * 78553 * 2
def baseEnd_78553 : Nat := 40335445852736394726247

theorem tailTrace_78553 : CollatzResearch.WordTrace tailWord_78553 prefixEnd_78553 40335445852736394726247 := by
  unfold tailWord_78553
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865063284423371629424313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1910042189615581086282875 2865063284423371629424313)
  ·
    refine ⟨2148797463317528722068235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2865063284423371629424313 2148797463317528722068235)
    ·
      refine ⟨3223196194976293083102353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148797463317528722068235 3223196194976293083102353)
      ·
        refine ⟨2417397146232219812326765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3223196194976293083102353 2417397146232219812326765)
        ·
          refine ⟨906523929837082429622537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2417397146232219812326765 906523929837082429622537)
          ·
            refine ⟨679892947377811822216903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906523929837082429622537 679892947377811822216903)
            ·
              refine ⟨1019839421066717733325355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 679892947377811822216903 1019839421066717733325355)
              ·
                refine ⟨1529759131600076599988033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1019839421066717733325355 1529759131600076599988033)
                ·
                  refine ⟨1147319348700057449991025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1529759131600076599988033 1147319348700057449991025)
                  ·
                    refine ⟨860489511525043087493269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1147319348700057449991025 860489511525043087493269)
                    ·
                      refine ⟨40335445852736394726247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 860489511525043087493269 40335445852736394726247)
                      ·
                        rfl

theorem cell23_78553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_78553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78553 prefixEnd_78553 := by exact prefixLift 78553
  have htrace : WordTrace (prefixWord ++ tailWord_78553) baseStart_78553 baseEnd_78553 := by
    simpa [prefixWord, tailWord_78553, baseEnd_78553] using wordTrace_append hprefix tailTrace_78553
  have hstable : (prefixWord ++ tailWord_78553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78553).length < 2 ^ (prefixWord ++ tailWord_78553).sum := by decide
  have hdescent : baseEnd_78553 < baseStart_78553 := by decide
  rcases family_descends (prefixWord ++ tailWord_78553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78560 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_78560 : Nat := 118140960795 + 78560 * 2 ^ 59
def prefixEnd_78560 : Nat := 4983230072969 + 3 ^ 40 * 78560 * 2
def baseEnd_78560 : Nat := 40339040217317867338715

theorem tailTrace_78560 : CollatzResearch.WordTrace tailWord_78560 prefixEnd_78560 40339040217317867338715 := by
  unfold tailWord_78560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432659297699005912464567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1910212396932007883286089 1432659297699005912464567)
  ·
    refine ⟨2148988946548508868696851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1432659297699005912464567 2148988946548508868696851)
    ·
      refine ⟨3223483419822763303045277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2148988946548508868696851 3223483419822763303045277)
      ·
        refine ⟨1208806282433536238641979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3223483419822763303045277 1208806282433536238641979)
        ·
          refine ⟨1813209423650304357962969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208806282433536238641979 1813209423650304357962969)
          ·
            refine ⟨1359907067737728268472227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1813209423650304357962969 1359907067737728268472227)
            ·
              refine ⟨2039860601606592402708341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1359907067737728268472227 2039860601606592402708341)
              ·
                refine ⟨191236931400618037753907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2039860601606592402708341 191236931400618037753907)
                ·
                  refine ⟨286855397100927056630861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191236931400618037753907 286855397100927056630861)
                  ·
                    refine ⟨107570773912847646236573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286855397100927056630861 107570773912847646236573)
                    ·
                      refine ⟨40339040217317867338715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 107570773912847646236573 40339040217317867338715)
                      ·
                        rfl

theorem cell23_78560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_78560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78560 prefixEnd_78560 := by exact prefixLift 78560
  have htrace : WordTrace (prefixWord ++ tailWord_78560) baseStart_78560 baseEnd_78560 := by
    simpa [prefixWord, tailWord_78560, baseEnd_78560] using wordTrace_append hprefix tailTrace_78560
  have hstable : (prefixWord ++ tailWord_78560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78560).length < 2 ^ (prefixWord ++ tailWord_78560).sum := by decide
  have hdescent : baseEnd_78560 < baseStart_78560 := by decide
  rcases family_descends (prefixWord ++ tailWord_78560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78564 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_78564 : Nat := 118140960795 + 78564 * 2 ^ 59
def prefixEnd_78564 : Nat := 4983230072969 + 3 ^ 40 * 78564 * 2
def baseEnd_78564 : Nat := 40341094139935851688697

theorem tailTrace_78564 : CollatzResearch.WordTrace tailWord_78564 prefixEnd_78564 40341094139935851688697 := by
  unfold tailWord_78564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432732243691760254037373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1910309658255680338716497 1432732243691760254037373)
  ·
    refine ⟨537274591384410095264015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1432732243691760254037373 537274591384410095264015)
    ·
      refine ⟨805911887076615142896023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537274591384410095264015 805911887076615142896023)
      ·
        refine ⟨1208867830614922714344035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805911887076615142896023 1208867830614922714344035)
        ·
          refine ⟨1813301745922384071516053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208867830614922714344035 1813301745922384071516053)
          ·
            refine ⟨84998519340111753352315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1813301745922384071516053 84998519340111753352315)
            ·
              refine ⟨127497779010167630028473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84998519340111753352315 127497779010167630028473)
              ·
                refine ⟨95623334257625722521355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127497779010167630028473 95623334257625722521355)
                ·
                  refine ⟨143435001386438583782033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95623334257625722521355 143435001386438583782033)
                  ·
                    refine ⟨107576251039828937836525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 143435001386438583782033 107576251039828937836525)
                    ·
                      refine ⟨40341094139935851688697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 107576251039828937836525 40341094139935851688697)
                      ·
                        rfl

theorem cell23_78564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_78564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78564 prefixEnd_78564 := by exact prefixLift 78564
  have htrace : WordTrace (prefixWord ++ tailWord_78564) baseStart_78564 baseEnd_78564 := by
    simpa [prefixWord, tailWord_78564, baseEnd_78564] using wordTrace_append hprefix tailTrace_78564
  have hstable : (prefixWord ++ tailWord_78564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78564).length < 2 ^ (prefixWord ++ tailWord_78564).sum := by decide
  have hdescent : baseEnd_78564 < baseStart_78564 := by decide
  rcases family_descends (prefixWord ++ tailWord_78564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78600 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_78600 : Nat := 118140960795 + 78600 * 2 ^ 59
def prefixEnd_78600 : Nat := 4983230072969 + 3 ^ 40 * 78600 * 2
def baseEnd_78600 : Nat := 40359579443497710838531

theorem tailTrace_78600 : CollatzResearch.WordTrace tailWord_78600 prefixEnd_78600 40359579443497710838531 := by
  unfold tailWord_78600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433388757626549328192627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1911185010168732437590169 1433388757626549328192627)
  ·
    refine ⟨2150083136439823992288941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1433388757626549328192627 2150083136439823992288941)
    ·
      refine ⟨806281176164933997108353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2150083136439823992288941 806281176164933997108353)
      ·
        refine ⟨604710882123700497831265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806281176164933997108353 604710882123700497831265)
        ·
          refine ⟨453533161592775373373449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604710882123700497831265 453533161592775373373449)
          ·
            refine ⟨340149871194581530030087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453533161592775373373449 340149871194581530030087)
            ·
              refine ⟨510224806791872295045131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340149871194581530030087 510224806791872295045131)
              ·
                refine ⟨765337210187808442567697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510224806791872295045131 765337210187808442567697)
                ·
                  refine ⟨574002907640856331925773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 765337210187808442567697 574002907640856331925773)
                  ·
                    refine ⟨215251090365321124472165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 574002907640856331925773 215251090365321124472165)
                    ·
                      refine ⟨40359579443497710838531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 215251090365321124472165 40359579443497710838531)
                      ·
                        rfl

theorem cell23_78600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_78600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78600 prefixEnd_78600 := by exact prefixLift 78600
  have htrace : WordTrace (prefixWord ++ tailWord_78600) baseStart_78600 baseEnd_78600 := by
    simpa [prefixWord, tailWord_78600, baseEnd_78600] using wordTrace_append hprefix tailTrace_78600
  have hstable : (prefixWord ++ tailWord_78600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78600).length < 2 ^ (prefixWord ++ tailWord_78600).sum := by decide
  have hdescent : baseEnd_78600 < baseStart_78600 := by decide
  rcases family_descends (prefixWord ++ tailWord_78600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78638 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_78638 : Nat := 118140960795 + 78638 * 2 ^ 59
def prefixEnd_78638 : Nat := 4983230072969 + 3 ^ 40 * 78638 * 2
def baseEnd_78638 : Nat := 40379091708368562163357

theorem tailTrace_78638 : CollatzResearch.WordTrace tailWord_78638 prefixEnd_78638 40379091708368562163357 := by
  unfold tailWord_78638
  simp only [CollatzResearch.WordTrace]
  refine ⟨358520436139428893283571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1912108992743620764179045 358520436139428893283571)
  ·
    refine ⟨537780654209143339925357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 358520436139428893283571 537780654209143339925357)
    ·
      refine ⟨201667745328428752472009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 537780654209143339925357 201667745328428752472009)
      ·
        refine ⟨151250808996321564354007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201667745328428752472009 151250808996321564354007)
        ·
          refine ⟨226876213494482346531011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151250808996321564354007 226876213494482346531011)
          ·
            refine ⟨340314320241723519796517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226876213494482346531011 340314320241723519796517)
            ·
              refine ⟨63808935045323159961847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 340314320241723519796517 63808935045323159961847)
              ·
                refine ⟨95713402567984739942771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63808935045323159961847 95713402567984739942771)
                ·
                  refine ⟨143570103851977109914157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95713402567984739942771 143570103851977109914157)
                  ·
                    refine ⟨53838788944491416217809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143570103851977109914157 53838788944491416217809)
                    ·
                      refine ⟨40379091708368562163357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53838788944491416217809 40379091708368562163357)
                      ·
                        rfl

theorem cell23_78638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_78638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78638 prefixEnd_78638 := by exact prefixLift 78638
  have htrace : WordTrace (prefixWord ++ tailWord_78638) baseStart_78638 baseEnd_78638 := by
    simpa [prefixWord, tailWord_78638, baseEnd_78638] using wordTrace_append hprefix tailTrace_78638
  have hstable : (prefixWord ++ tailWord_78638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78638).length < 2 ^ (prefixWord ++ tailWord_78638).sum := by decide
  have hdescent : baseEnd_78638 < baseStart_78638 := by decide
  rcases family_descends (prefixWord ++ tailWord_78638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78668 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 2, 2, 2]
def baseStart_78668 : Nat := 118140960795 + 78668 * 2 ^ 59
def prefixEnd_78668 : Nat := 4983230072969 + 3 ^ 40 * 78668 * 2
def baseEnd_78668 : Nat := 40394496128003444788219

theorem tailTrace_78668 : CollatzResearch.WordTrace tailWord_78668 prefixEnd_78668 40394496128003444788219 := by
  unfold tailWord_78668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434628839503373134930329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1912838452671164179907105 1434628839503373134930329)
  ·
    refine ⟨1075971629627529851197747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1434628839503373134930329 1075971629627529851197747)
    ·
      refine ⟨1613957444441294776796621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075971629627529851197747 1613957444441294776796621)
      ·
        refine ⟨605234041665485541298733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1613957444441294776796621 605234041665485541298733)
        ·
          refine ⟨226962765624557077987025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 605234041665485541298733 226962765624557077987025)
          ·
            refine ⟨170222074218417808490269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226962765624557077987025 170222074218417808490269)
            ·
              refine ⟨63833277831906678183851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170222074218417808490269 63833277831906678183851)
              ·
                refine ⟨95749916747860017275777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63833277831906678183851 95749916747860017275777)
                ·
                  refine ⟨71812437560895012956833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95749916747860017275777 71812437560895012956833)
                  ·
                    refine ⟨53859328170671259717625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71812437560895012956833 53859328170671259717625)
                    ·
                      refine ⟨40394496128003444788219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53859328170671259717625 40394496128003444788219)
                      ·
                        rfl

theorem cell23_78668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_78668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78668 prefixEnd_78668 := by exact prefixLift 78668
  have htrace : WordTrace (prefixWord ++ tailWord_78668) baseStart_78668 baseEnd_78668 := by
    simpa [prefixWord, tailWord_78668, baseEnd_78668] using wordTrace_append hprefix tailTrace_78668
  have hstable : (prefixWord ++ tailWord_78668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78668).length < 2 ^ (prefixWord ++ tailWord_78668).sum := by decide
  have hdescent : baseEnd_78668 < baseStart_78668 := by decide
  rcases family_descends (prefixWord ++ tailWord_78668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78707 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 4, 4, 2]
def baseStart_78707 : Nat := 118140960795 + 78707 * 2 ^ 59
def prefixEnd_78707 : Nat := 4983230072969 + 3 ^ 40 * 78707 * 2
def baseEnd_78707 : Nat := 40414521873528792200539

theorem tailTrace_78707 : CollatzResearch.WordTrace tailWord_78707 prefixEnd_78707 40414521873528792200539 := by
  unfold tailWord_78707
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870680125865455930530375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1913786750576970620353583 2870680125865455930530375)
  ·
    refine ⟨4306020188798183895795563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2870680125865455930530375 4306020188798183895795563)
    ·
      refine ⟨6459030283197275843693345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4306020188798183895795563 6459030283197275843693345)
      ·
        refine ⟨4844272712397956882770009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6459030283197275843693345 4844272712397956882770009)
        ·
          refine ⟨3633204534298467662077507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844272712397956882770009 3633204534298467662077507)
          ·
            refine ⟨5449806801447701493116261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3633204534298467662077507 5449806801447701493116261)
            ·
              refine ⟨1021838775271444029959299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5449806801447701493116261 1021838775271444029959299)
              ·
                refine ⟨1532758162907166044938949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1021838775271444029959299 1532758162907166044938949)
                ·
                  refine ⟨287392155545093633426053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1532758162907166044938949 287392155545093633426053)
                  ·
                    refine ⟨53886029164705056267385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287392155545093633426053 53886029164705056267385)
                    ·
                      refine ⟨40414521873528792200539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53886029164705056267385 40414521873528792200539)
                      ·
                        rfl

theorem cell23_78707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4, 2].length) (baseStart_78707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78707 prefixEnd_78707 := by exact prefixLift 78707
  have htrace : WordTrace (prefixWord ++ tailWord_78707) baseStart_78707 baseEnd_78707 := by
    simpa [prefixWord, tailWord_78707, baseEnd_78707] using wordTrace_append hprefix tailTrace_78707
  have hstable : (prefixWord ++ tailWord_78707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78707).length < 2 ^ (prefixWord ++ tailWord_78707).sum := by decide
  have hdescent : baseEnd_78707 < baseStart_78707 := by decide
  rcases family_descends (prefixWord ++ tailWord_78707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78720 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_78720 : Nat := 118140960795 + 78720 * 2 ^ 59
def prefixEnd_78720 : Nat := 4983230072969 + 3 ^ 40 * 78720 * 2
def baseEnd_78720 : Nat := 40421197122037241337979

theorem tailTrace_78720 : CollatzResearch.WordTrace tailWord_78720 prefixEnd_78720 40421197122037241337979 := by
  unfold tailWord_78720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435577137409179575376807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1914102849878906100502409 1435577137409179575376807)
  ·
    refine ⟨2153365706113769363065211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435577137409179575376807 2153365706113769363065211)
    ·
      refine ⟨3230048559170654044597817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2153365706113769363065211 3230048559170654044597817)
      ·
        refine ⟨2422536419377990533448363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3230048559170654044597817 2422536419377990533448363)
        ·
          refine ⟨3633804629066985800172545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2422536419377990533448363 3633804629066985800172545)
          ·
            refine ⟨2725353471800239350129409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3633804629066985800172545 2725353471800239350129409)
            ·
              refine ⟨2044015103850179512597057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2725353471800239350129409 2044015103850179512597057)
              ·
                refine ⟨1533011327887634634447793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2044015103850179512597057 1533011327887634634447793)
                ·
                  refine ⟨1149758495915725975835845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1533011327887634634447793 1149758495915725975835845)
                  ·
                    refine ⟨215579717984198620469221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1149758495915725975835845 215579717984198620469221)
                    ·
                      refine ⟨40421197122037241337979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 215579717984198620469221 40421197122037241337979)
                      ·
                        rfl

theorem cell23_78720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_78720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78720 prefixEnd_78720 := by exact prefixLift 78720
  have htrace : WordTrace (prefixWord ++ tailWord_78720) baseStart_78720 baseEnd_78720 := by
    simpa [prefixWord, tailWord_78720, baseEnd_78720] using wordTrace_append hprefix tailTrace_78720
  have hstable : (prefixWord ++ tailWord_78720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78720).length < 2 ^ (prefixWord ++ tailWord_78720).sum := by decide
  have hdescent : baseEnd_78720 < baseStart_78720 := by decide
  rcases family_descends (prefixWord ++ tailWord_78720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78777 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_78777 : Nat := 118140960795 + 78777 * 2 ^ 59
def prefixEnd_78777 : Nat := 4983230072969 + 3 ^ 40 * 78777 * 2
def baseEnd_78777 : Nat := 13483488506447839441739

theorem tailTrace_78777 : CollatzResearch.WordTrace tailWord_78777 prefixEnd_78777 13483488506447839441739 := by
  unfold tailWord_78777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873233235611857885578585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1915488823741238590385723 2873233235611857885578585)
  ·
    refine ⟨2154924926708893414183939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2873233235611857885578585 2154924926708893414183939)
    ·
      refine ⟨3232387390063340121275909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2154924926708893414183939 3232387390063340121275909)
      ·
        refine ⟨606072635636876272739233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3232387390063340121275909 606072635636876272739233)
        ·
          refine ⟨454554476727657204554425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606072635636876272739233 454554476727657204554425)
          ·
            refine ⟨340915857545742903415819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454554476727657204554425 340915857545742903415819)
            ·
              refine ⟨511373786318614355123729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340915857545742903415819 511373786318614355123729)
              ·
                refine ⟨383530339738960766342797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 511373786318614355123729 383530339738960766342797)
                ·
                  refine ⟨143823877402110287378549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 383530339738960766342797 143823877402110287378549)
                  ·
                    refine ⟨13483488506447839441739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 143823877402110287378549 13483488506447839441739)
                    ·
                      rfl

theorem cell23_78777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_78777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78777 prefixEnd_78777 := by exact prefixLift 78777
  have htrace : WordTrace (prefixWord ++ tailWord_78777) baseStart_78777 baseEnd_78777 := by
    simpa [prefixWord, tailWord_78777, baseEnd_78777] using wordTrace_append hprefix tailTrace_78777
  have hstable : (prefixWord ++ tailWord_78777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78777).length < 2 ^ (prefixWord ++ tailWord_78777).sum := by decide
  have hdescent : baseEnd_78777 < baseStart_78777 := by decide
  rcases family_descends (prefixWord ++ tailWord_78777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78808 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 1, 1, 3]
def baseStart_78808 : Nat := 118140960795 + 78808 * 2 ^ 59
def prefixEnd_78808 : Nat := 4983230072969 + 3 ^ 40 * 78808 * 2
def baseEnd_78808 : Nat := 40466383419632897037575

theorem tailTrace_78808 : CollatzResearch.WordTrace tailWord_78808 prefixEnd_78808 40466383419632897037575 := by
  unfold tailWord_78808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437181949249775089978539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1916242598999700119971385 1437181949249775089978539)
  ·
    refine ⟨2155772923874662634967809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1437181949249775089978539 2155772923874662634967809)
    ·
      refine ⟨1616829692905996976225857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155772923874662634967809 1616829692905996976225857)
      ·
        refine ⟨1212622269679497732169393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1616829692905996976225857 1212622269679497732169393)
        ·
          refine ⟨909466702259623299127045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212622269679497732169393 909466702259623299127045)
          ·
            refine ⟨170525006673679368586321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 909466702259623299127045 170525006673679368586321)
            ·
              refine ⟨127893755005259526439741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170525006673679368586321 127893755005259526439741)
              ·
                refine ⟨47960158126972322414903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127893755005259526439741 47960158126972322414903)
                ·
                  refine ⟨71940237190458483622355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47960158126972322414903 71940237190458483622355)
                  ·
                    refine ⟨107910355785687725433533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71940237190458483622355 107910355785687725433533)
                    ·
                      refine ⟨40466383419632897037575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 107910355785687725433533 40466383419632897037575)
                      ·
                        rfl

theorem cell23_78808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_78808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78808 prefixEnd_78808 := by exact prefixLift 78808
  have htrace : WordTrace (prefixWord ++ tailWord_78808) baseStart_78808 baseEnd_78808 := by
    simpa [prefixWord, tailWord_78808, baseEnd_78808] using wordTrace_append hprefix tailTrace_78808
  have hstable : (prefixWord ++ tailWord_78808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78808).length < 2 ^ (prefixWord ++ tailWord_78808).sum := by decide
  have hdescent : baseEnd_78808 < baseStart_78808 := by decide
  rcases family_descends (prefixWord ++ tailWord_78808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78817 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_78817 : Nat := 118140960795 + 78817 * 2 ^ 59
def prefixEnd_78817 : Nat := 4983230072969 + 3 ^ 40 * 78817 * 2
def baseEnd_78817 : Nat := 40471004745523361825033

theorem tailTrace_78817 : CollatzResearch.WordTrace tailWord_78817 prefixEnd_78817 40471004745523361825033 := by
  unfold tailWord_78817
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874692155466944717034705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1916461436977963144689803 2874692155466944717034705)
  ·
    refine ⟨2156019116600208537776029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2874692155466944717034705 2156019116600208537776029)
    ·
      refine ⟨808507168725078201666011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2156019116600208537776029 808507168725078201666011)
      ·
        refine ⟨1212760753087617302499017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808507168725078201666011 1212760753087617302499017)
        ·
          refine ⟨909570564815712976874263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1212760753087617302499017 909570564815712976874263)
          ·
            refine ⟨1364355847223569465311395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909570564815712976874263 1364355847223569465311395)
            ·
              refine ⟨2046533770835354197967093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1364355847223569465311395 2046533770835354197967093)
              ·
                refine ⟨191862541015814456059415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2046533770835354197967093 191862541015814456059415)
                ·
                  refine ⟨287793811523721684089123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191862541015814456059415 287793811523721684089123)
                  ·
                    refine ⟨431690717285582526133685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 287793811523721684089123 431690717285582526133685)
                    ·
                      refine ⟨40471004745523361825033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 431690717285582526133685 40471004745523361825033)
                      ·
                        rfl

theorem cell23_78817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_78817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78817 prefixEnd_78817 := by exact prefixLift 78817
  have htrace : WordTrace (prefixWord ++ tailWord_78817) baseStart_78817 baseEnd_78817 := by
    simpa [prefixWord, tailWord_78817, baseEnd_78817] using wordTrace_append hprefix tailTrace_78817
  have hstable : (prefixWord ++ tailWord_78817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78817).length < 2 ^ (prefixWord ++ tailWord_78817).sum := by decide
  have hdescent : baseEnd_78817 < baseStart_78817 := by decide
  rcases family_descends (prefixWord ++ tailWord_78817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78831 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 3, 2, 2]
def baseStart_78831 : Nat := 118140960795 + 78831 * 2 ^ 59
def prefixEnd_78831 : Nat := 4983230072969 + 3 ^ 40 * 78831 * 2
def baseEnd_78831 : Nat := 40478193474686307049969

theorem tailTrace_78831 : CollatzResearch.WordTrace tailWord_78831 prefixEnd_78831 40478193474686307049969 := by
  unfold tailWord_78831
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875202777416225108044347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1916801851610816738696231 2875202777416225108044347)
  ·
    refine ⟨4312804166124337662066521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2875202777416225108044347 4312804166124337662066521)
    ·
      refine ⟨3234603124593253246549891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4312804166124337662066521 3234603124593253246549891)
      ·
        refine ⟨4851904686889879869824837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3234603124593253246549891 4851904686889879869824837)
        ·
          refine ⟨909732128791852475592157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4851904686889879869824837 909732128791852475592157)
          ·
            refine ⟨341149548296944678347059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 909732128791852475592157 341149548296944678347059)
            ·
              refine ⟨511724322445417017520589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341149548296944678347059 511724322445417017520589)
              ·
                refine ⟨191896620917031381570221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 511724322445417017520589 191896620917031381570221)
                ·
                  refine ⟨71961232843886768088833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191896620917031381570221 71961232843886768088833)
                  ·
                    refine ⟨53970924632915076066625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71961232843886768088833 53970924632915076066625)
                    ·
                      refine ⟨40478193474686307049969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 53970924632915076066625 40478193474686307049969)
                      ·
                        rfl

theorem cell23_78831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 2, 2].length) (baseStart_78831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78831 prefixEnd_78831 := by exact prefixLift 78831
  have htrace : WordTrace (prefixWord ++ tailWord_78831) baseStart_78831 baseEnd_78831 := by
    simpa [prefixWord, tailWord_78831, baseEnd_78831] using wordTrace_append hprefix tailTrace_78831
  have hstable : (prefixWord ++ tailWord_78831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78831).length < 2 ^ (prefixWord ++ tailWord_78831).sum := by decide
  have hdescent : baseEnd_78831 < baseStart_78831 := by decide
  rcases family_descends (prefixWord ++ tailWord_78831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78841 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 2, 4]
def baseStart_78841 : Nat := 118140960795 + 78841 * 2 ^ 59
def prefixEnd_78841 : Nat := 4983230072969 + 3 ^ 40 * 78841 * 2
def baseEnd_78841 : Nat := 13494442760410422641641

theorem tailTrace_78841 : CollatzResearch.WordTrace tailWord_78841 prefixEnd_78841 13494442760410422641641 := by
  unfold tailWord_78841
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875567507379996815908377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1917045004919997877272251 2875567507379996815908377)
  ·
    refine ⟨2156675630534997611931283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2875567507379996815908377 2156675630534997611931283)
    ·
      refine ⟨3235013445802496417896925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2156675630534997611931283 3235013445802496417896925)
      ·
        refine ⟨1213130042175936156711347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3235013445802496417896925 1213130042175936156711347)
        ·
          refine ⟨1819695063263904235067021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213130042175936156711347 1819695063263904235067021)
          ·
            refine ⟨682385648723964088150133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1819695063263904235067021 682385648723964088150133)
            ·
              refine ⟨63973654567871633264075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 682385648723964088150133 63973654567871633264075)
              ·
                refine ⟨95960481851807449896113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63973654567871633264075 95960481851807449896113)
                ·
                  refine ⟨71970361388855587422085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95960481851807449896113 71970361388855587422085)
                  ·
                    refine ⟨13494442760410422641641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71970361388855587422085 13494442760410422641641)
                    ·
                      rfl

theorem cell23_78841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 4].length) (baseStart_78841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78841 prefixEnd_78841 := by exact prefixLift 78841
  have htrace : WordTrace (prefixWord ++ tailWord_78841) baseStart_78841 baseEnd_78841 := by
    simpa [prefixWord, tailWord_78841, baseEnd_78841] using wordTrace_append hprefix tailTrace_78841
  have hstable : (prefixWord ++ tailWord_78841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78841).length < 2 ^ (prefixWord ++ tailWord_78841).sum := by decide
  have hdescent : baseEnd_78841 < baseStart_78841 := by decide
  rcases family_descends (prefixWord ++ tailWord_78841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78844 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_78844 : Nat := 118140960795 + 78844 * 2 ^ 59
def prefixEnd_78844 : Nat := 4983230072969 + 3 ^ 40 * 78844 * 2
def baseEnd_78844 : Nat := 40484868723194756187409

theorem tailTrace_78844 : CollatzResearch.WordTrace tailWord_78844 prefixEnd_78844 40484868723194756187409 := by
  unfold tailWord_78844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437838463184564164133793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1917117950912752218845057 1437838463184564164133793)
  ·
    refine ⟨1078378847388423123100345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1437838463184564164133793 1078378847388423123100345)
    ·
      refine ⟨808784135541317342325259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078378847388423123100345 808784135541317342325259)
      ·
        refine ⟨1213176203311976013487889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808784135541317342325259 1213176203311976013487889)
        ·
          refine ⟨909882152483982010115917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1213176203311976013487889 909882152483982010115917)
          ·
            refine ⟨341205807181493253793469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 909882152483982010115917 341205807181493253793469)
            ·
              refine ⟨127952177693059970172551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341205807181493253793469 127952177693059970172551)
              ·
                refine ⟨191928266539589955258827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127952177693059970172551 191928266539589955258827)
                ·
                  refine ⟨287892399809384932888241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191928266539589955258827 287892399809384932888241)
                  ·
                    refine ⟨215919299857038699666181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 287892399809384932888241 215919299857038699666181)
                    ·
                      refine ⟨40484868723194756187409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 215919299857038699666181 40484868723194756187409)
                      ·
                        rfl

theorem cell23_78844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_78844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78844 prefixEnd_78844 := by exact prefixLift 78844
  have htrace : WordTrace (prefixWord ++ tailWord_78844) baseStart_78844 baseEnd_78844 := by
    simpa [prefixWord, tailWord_78844, baseEnd_78844] using wordTrace_append hprefix tailTrace_78844
  have hstable : (prefixWord ++ tailWord_78844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78844).length < 2 ^ (prefixWord ++ tailWord_78844).sum := by decide
  have hdescent : baseEnd_78844 < baseStart_78844 := by decide
  rcases family_descends (prefixWord ++ tailWord_78844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78881 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_78881 : Nat := 118140960795 + 78881 * 2 ^ 59
def prefixEnd_78881 : Nat := 4983230072969 + 3 ^ 40 * 78881 * 2
def baseEnd_78881 : Nat := 40503867507411111424739

theorem tailTrace_78881 : CollatzResearch.WordTrace tailWord_78881 prefixEnd_78881 40503867507411111424739 := by
  unfold tailWord_78881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877026427235083647364497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1918017618156722431576331 2877026427235083647364497)
  ·
    refine ⟨2157769820426312735523373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2877026427235083647364497 2157769820426312735523373)
    ·
      refine ⟨809163682659867275821265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2157769820426312735523373 809163682659867275821265)
      ·
        refine ⟨606872761994900456865949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809163682659867275821265 606872761994900456865949)
        ·
          refine ⟨227577285748087671324731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606872761994900456865949 227577285748087671324731)
          ·
            refine ⟨341365928622131506987097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227577285748087671324731 341365928622131506987097)
            ·
              refine ⟨256024446466598630240323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341365928622131506987097 256024446466598630240323)
              ·
                refine ⟨384036669699897945360485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256024446466598630240323 384036669699897945360485)
                ·
                  refine ⟨72006875568730864755091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384036669699897945360485 72006875568730864755091)
                  ·
                    refine ⟨108010313353096297132637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72006875568730864755091 108010313353096297132637)
                    ·
                      refine ⟨40503867507411111424739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108010313353096297132637 40503867507411111424739)
                      ·
                        rfl

theorem cell23_78881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_78881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78881 prefixEnd_78881 := by exact prefixLift 78881
  have htrace : WordTrace (prefixWord ++ tailWord_78881) baseStart_78881 baseEnd_78881 := by
    simpa [prefixWord, tailWord_78881, baseEnd_78881] using wordTrace_append hprefix tailTrace_78881
  have hstable : (prefixWord ++ tailWord_78881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78881).length < 2 ^ (prefixWord ++ tailWord_78881).sum := by decide
  have hdescent : baseEnd_78881 < baseStart_78881 := by decide
  rcases family_descends (prefixWord ++ tailWord_78881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78882 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_78882 : Nat := 118140960795 + 78882 * 2 ^ 59
def prefixEnd_78882 : Nat := 4983230072969 + 3 ^ 40 * 78882 * 2
def baseEnd_78882 : Nat := 40504380988065607512235

theorem tailTrace_78882 : CollatzResearch.WordTrace tailWord_78882 prefixEnd_78882 40504380988065607512235 := by
  unfold tailWord_78882
  simp only [CollatzResearch.WordTrace]
  refine ⟨719265725057865204537725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1918041933487640545433933 719265725057865204537725)
  ·
    refine ⟨269724646896699451701647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 719265725057865204537725 269724646896699451701647)
    ·
      refine ⟨404586970345049177552471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269724646896699451701647 404586970345049177552471)
      ·
        refine ⟨606880455517573766328707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404586970345049177552471 606880455517573766328707)
        ·
          refine ⟨910320683276360649493061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606880455517573766328707 910320683276360649493061)
          ·
            refine ⟨170685128114317621779949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 910320683276360649493061 170685128114317621779949)
            ·
              refine ⟨64006923042869108167481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170685128114317621779949 64006923042869108167481)
              ·
                refine ⟨48005192282151831125611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64006923042869108167481 48005192282151831125611)
                ·
                  refine ⟨72007788423227746688417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48005192282151831125611 72007788423227746688417)
                  ·
                    refine ⟨54005841317420810016313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72007788423227746688417 54005841317420810016313)
                    ·
                      refine ⟨40504380988065607512235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54005841317420810016313 40504380988065607512235)
                      ·
                        rfl

theorem cell23_78882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_78882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78882 prefixEnd_78882 := by exact prefixLift 78882
  have htrace : WordTrace (prefixWord ++ tailWord_78882) baseStart_78882 baseEnd_78882 := by
    simpa [prefixWord, tailWord_78882, baseEnd_78882] using wordTrace_append hprefix tailTrace_78882
  have hstable : (prefixWord ++ tailWord_78882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78882).length < 2 ^ (prefixWord ++ tailWord_78882).sum := by decide
  have hdescent : baseEnd_78882 < baseStart_78882 := by decide
  rcases family_descends (prefixWord ++ tailWord_78882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78897 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_78897 : Nat := 118140960795 + 78897 * 2 ^ 59
def prefixEnd_78897 : Nat := 4983230072969 + 3 ^ 40 * 78897 * 2
def baseEnd_78897 : Nat := 13504027732627682941555

theorem tailTrace_78897 : CollatzResearch.WordTrace tailWord_78897 prefixEnd_78897 13504027732627682941555 := by
  unfold tailWord_78897
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877609995177118379946945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1918406663451412253297963 2877609995177118379946945)
  ·
    refine ⟨2158207496382838784960209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2877609995177118379946945 2158207496382838784960209)
    ·
      refine ⟨1618655622287129088720157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158207496382838784960209 1618655622287129088720157)
      ·
        refine ⟨606995858357673408270059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1618655622287129088720157 606995858357673408270059)
        ·
          refine ⟨910493787536510112405089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606995858357673408270059 910493787536510112405089)
          ·
            refine ⟨682870340652382584303817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910493787536510112405089 682870340652382584303817)
            ·
              refine ⟨512152755489286938227863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682870340652382584303817 512152755489286938227863)
              ·
                refine ⟨768229133233930407341795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512152755489286938227863 768229133233930407341795)
                ·
                  refine ⟨1152343699850895611012693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 768229133233930407341795 1152343699850895611012693)
                  ·
                    refine ⟨13504027732627682941555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1152343699850895611012693 13504027732627682941555)
                    ·
                      rfl

theorem cell23_78897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_78897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78897 prefixEnd_78897 := by exact prefixLift 78897
  have htrace : WordTrace (prefixWord ++ tailWord_78897) baseStart_78897 baseEnd_78897 := by
    simpa [prefixWord, tailWord_78897, baseEnd_78897] using wordTrace_append hprefix tailTrace_78897
  have hstable : (prefixWord ++ tailWord_78897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78897).length < 2 ^ (prefixWord ++ tailWord_78897).sum := by decide
  have hdescent : baseEnd_78897 < baseStart_78897 := by decide
  rcases family_descends (prefixWord ++ tailWord_78897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78908 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_78908 : Nat := 118140960795 + 78908 * 2 ^ 59
def prefixEnd_78908 : Nat := 4983230072969 + 3 ^ 40 * 78908 * 2
def baseEnd_78908 : Nat := 40517731485082505787115

theorem tailTrace_78908 : CollatzResearch.WordTrace tailWord_78908 prefixEnd_78908 40517731485082505787115 := by
  unfold tailWord_78908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439005599068633629298689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1918674132091511505731585 1439005599068633629298689)
  ·
    refine ⟨1079254199301475221974017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1439005599068633629298689 1079254199301475221974017)
    ·
      refine ⟨809440649476106416480513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079254199301475221974017 809440649476106416480513)
      ·
        refine ⟨607080487107079812360385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 809440649476106416480513 607080487107079812360385)
        ·
          refine ⟨455310365330309859270289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607080487107079812360385 455310365330309859270289)
          ·
            refine ⟨341482773997732394452717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455310365330309859270289 341482773997732394452717)
            ·
              refine ⟨128056040249149647919769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341482773997732394452717 128056040249149647919769)
              ·
                refine ⟨96042030186862235939827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128056040249149647919769 96042030186862235939827)
                ·
                  refine ⟨144063045280293353909741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96042030186862235939827 144063045280293353909741)
                  ·
                    refine ⟨54023641980110007716153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144063045280293353909741 54023641980110007716153)
                    ·
                      refine ⟨40517731485082505787115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54023641980110007716153 40517731485082505787115)
                      ·
                        rfl

theorem cell23_78908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_78908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78908 prefixEnd_78908 := by exact prefixLift 78908
  have htrace : WordTrace (prefixWord ++ tailWord_78908) baseStart_78908 baseEnd_78908 := by
    simpa [prefixWord, tailWord_78908, baseEnd_78908] using wordTrace_append hprefix tailTrace_78908
  have hstable : (prefixWord ++ tailWord_78908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78908).length < 2 ^ (prefixWord ++ tailWord_78908).sum := by decide
  have hdescent : baseEnd_78908 < baseStart_78908 := by decide
  rcases family_descends (prefixWord ++ tailWord_78908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78921 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 4, 2, 2]
def baseStart_78921 : Nat := 118140960795 + 78921 * 2 ^ 59
def prefixEnd_78921 : Nat := 4983230072969 + 3 ^ 40 * 78921 * 2
def baseEnd_78921 : Nat := 40524406733590954924555

theorem tailTrace_78921 : CollatzResearch.WordTrace tailWord_78921 prefixEnd_78921 40524406733590954924555 := by
  unfold tailWord_78921
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878485347090170478820617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1918990231393446985880411 2878485347090170478820617)
  ·
    refine ⟨2158864010317627859115463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2878485347090170478820617 2158864010317627859115463)
    ·
      refine ⟨3238296015476441788673195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2158864010317627859115463 3238296015476441788673195)
      ·
        refine ⟨4857444023214662683009793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238296015476441788673195 4857444023214662683009793)
        ·
          refine ⟨3643083017410997012257345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4857444023214662683009793 3643083017410997012257345)
          ·
            refine ⟨2732312263058247759193009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3643083017410997012257345 2732312263058247759193009)
            ·
              refine ⟨2049234197293685819394757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2732312263058247759193009 2049234197293685819394757)
              ·
                refine ⟨384231411992566091136517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2049234197293685819394757 384231411992566091136517)
                ·
                  refine ⟨72043389748606142088097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384231411992566091136517 72043389748606142088097)
                  ·
                    refine ⟨54032542311454606566073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72043389748606142088097 54032542311454606566073)
                    ·
                      refine ⟨40524406733590954924555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54032542311454606566073 40524406733590954924555)
                      ·
                        rfl

theorem cell23_78921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 2, 2].length) (baseStart_78921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78921 prefixEnd_78921 := by exact prefixLift 78921
  have htrace : WordTrace (prefixWord ++ tailWord_78921) baseStart_78921 baseEnd_78921 := by
    simpa [prefixWord, tailWord_78921, baseEnd_78921] using wordTrace_append hprefix tailTrace_78921
  have hstable : (prefixWord ++ tailWord_78921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78921).length < 2 ^ (prefixWord ++ tailWord_78921).sum := by decide
  have hdescent : baseEnd_78921 < baseStart_78921 := by decide
  rcases family_descends (prefixWord ++ tailWord_78921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78947 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_78947 : Nat := 118140960795 + 78947 * 2 ^ 59
def prefixEnd_78947 : Nat := 4983230072969 + 3 ^ 40 * 78947 * 2
def baseEnd_78947 : Nat := 40537757230607853199435

theorem tailTrace_78947 : CollatzResearch.WordTrace tailWord_78947 prefixEnd_78947 40537757230607853199435 := by
  unfold tailWord_78947
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879433644995976919267095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1919622429997317946178063 2879433644995976919267095)
  ·
    refine ⟨4319150467493965378900643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2879433644995976919267095 4319150467493965378900643)
    ·
      refine ⟨6478725701240948068350965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4319150467493965378900643 6478725701240948068350965)
      ·
        refine ⟨607380534491338881407903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6478725701240948068350965 607380534491338881407903)
        ·
          refine ⟨911070801737008322111855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607380534491338881407903 911070801737008322111855)
          ·
            refine ⟨1366606202605512483167783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 911070801737008322111855 1366606202605512483167783)
            ·
              refine ⟨2049909303908268724751675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1366606202605512483167783 2049909303908268724751675)
              ·
                refine ⟨3074863955862403087127513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049909303908268724751675 3074863955862403087127513)
                ·
                  refine ⟨2306147966896802315345635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3074863955862403087127513 2306147966896802315345635)
                  ·
                    refine ⟨3459221950345203473018453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306147966896802315345635 3459221950345203473018453)
                    ·
                      refine ⟨40537757230607853199435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 3459221950345203473018453 40537757230607853199435)
                      ·
                        rfl

theorem cell23_78947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_78947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78947 prefixEnd_78947 := by exact prefixLift 78947
  have htrace : WordTrace (prefixWord ++ tailWord_78947) baseStart_78947 baseEnd_78947 := by
    simpa [prefixWord, tailWord_78947, baseEnd_78947] using wordTrace_append hprefix tailTrace_78947
  have hstable : (prefixWord ++ tailWord_78947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78947).length < 2 ^ (prefixWord ++ tailWord_78947).sum := by decide
  have hdescent : baseEnd_78947 < baseStart_78947 := by decide
  rcases family_descends (prefixWord ++ tailWord_78947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78987 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 10]
def baseStart_78987 : Nat := 118140960795 + 78987 * 2 ^ 59
def prefixEnd_78987 : Nat := 4983230072969 + 3 ^ 40 * 78987 * 2
def baseEnd_78987 : Nat := 13519432152262565566417

theorem tailTrace_78987 : CollatzResearch.WordTrace tailWord_78987 prefixEnd_78987 13519432152262565566417 := by
  unfold tailWord_78987
  simp only [CollatzResearch.WordTrace]
  refine ⟨2880892564851063750723215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1920595043234042500482143 2880892564851063750723215)
  ·
    refine ⟨4321338847276595626084823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2880892564851063750723215 4321338847276595626084823)
    ·
      refine ⟨6482008270914893439127235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4321338847276595626084823 6482008270914893439127235)
      ·
        refine ⟨9723012406372340158690853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482008270914893439127235 9723012406372340158690853)
        ·
          refine ⟨1823064826194813779754535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9723012406372340158690853 1823064826194813779754535)
          ·
            refine ⟨2734597239292220669631803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823064826194813779754535 2734597239292220669631803)
            ·
              refine ⟨4101895858938331004447705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734597239292220669631803 4101895858938331004447705)
              ·
                refine ⟨3076421894203748253335779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101895858938331004447705 3076421894203748253335779)
                ·
                  refine ⟨4614632841305622380003669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076421894203748253335779 4614632841305622380003669)
                  ·
                    refine ⟨13519432152262565566417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 4614632841305622380003669 13519432152262565566417)
                    ·
                      rfl

theorem cell23_78987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_78987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_78987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_78987 prefixEnd_78987 := by exact prefixLift 78987
  have htrace : WordTrace (prefixWord ++ tailWord_78987) baseStart_78987 baseEnd_78987 := by
    simpa [prefixWord, tailWord_78987, baseEnd_78987] using wordTrace_append hprefix tailTrace_78987
  have hstable : (prefixWord ++ tailWord_78987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78987).length < 2 ^ (prefixWord ++ tailWord_78987).sum := by decide
  have hdescent : baseEnd_78987 < baseStart_78987 := by decide
  rcases family_descends (prefixWord ++ tailWord_78987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79031 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_79031 : Nat := 118140960795 + 79031 * 2 ^ 59
def prefixEnd_79031 : Nat := 4983230072969 + 3 ^ 40 * 79031 * 2
def baseEnd_79031 : Nat := 40580889605585524549049

theorem tailTrace_79031 : CollatzResearch.WordTrace tailWord_79031 prefixEnd_79031 40580889605585524549049 := by
  unfold tailWord_79031
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882497376691659265324947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1921664917794439510216631 2882497376691659265324947)
  ·
    refine ⟨4323746065037488897987421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882497376691659265324947 4323746065037488897987421)
    ·
      refine ⟨1621404774389058336745283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4323746065037488897987421 1621404774389058336745283)
      ·
        refine ⟨2432107161583587505117925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621404774389058336745283 2432107161583587505117925)
        ·
          refine ⟨456020092796922657209611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2432107161583587505117925 456020092796922657209611)
          ·
            refine ⟨684030139195383985814417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456020092796922657209611 684030139195383985814417)
            ·
              refine ⟨513022604396537989360813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684030139195383985814417 513022604396537989360813)
              ·
                refine ⟨192383476648701746010305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 513022604396537989360813 192383476648701746010305)
                ·
                  refine ⟨144287607486526309507729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192383476648701746010305 144287607486526309507729)
                  ·
                    refine ⟨108215705614894732130797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144287607486526309507729 108215705614894732130797)
                    ·
                      refine ⟨40580889605585524549049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108215705614894732130797 40580889605585524549049)
                      ·
                        rfl

theorem cell23_79031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_79031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79031 prefixEnd_79031 := by exact prefixLift 79031
  have htrace : WordTrace (prefixWord ++ tailWord_79031) baseStart_79031 baseEnd_79031 := by
    simpa [prefixWord, tailWord_79031, baseEnd_79031] using wordTrace_append hprefix tailTrace_79031
  have hstable : (prefixWord ++ tailWord_79031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79031).length < 2 ^ (prefixWord ++ tailWord_79031).sum := by decide
  have hdescent : baseEnd_79031 < baseStart_79031 := by decide
  rcases family_descends (prefixWord ++ tailWord_79031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79071 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 3, 5, 2]
def baseStart_79071 : Nat := 118140960795 + 79071 * 2 ^ 59
def prefixEnd_79071 : Nat := 4983230072969 + 3 ^ 40 * 79071 * 2
def baseEnd_79071 : Nat := 40601428831765368048865

theorem tailTrace_79071 : CollatzResearch.WordTrace tailWord_79071 prefixEnd_79071 40601428831765368048865 := by
  unfold tailWord_79071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883956296546746096781067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1922637531031164064520711 2883956296546746096781067)
  ·
    refine ⟨4325934444820119145171601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2883956296546746096781067 4325934444820119145171601)
    ·
      refine ⟨3244450833615089358878701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4325934444820119145171601 3244450833615089358878701)
      ·
        refine ⟨1216669062605658509579513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3244450833615089358878701 1216669062605658509579513)
        ·
          refine ⟨912501796954243882184635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216669062605658509579513 912501796954243882184635)
          ·
            refine ⟨1368752695431365823276953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912501796954243882184635 1368752695431365823276953)
            ·
              refine ⟨1026564521573524367457715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368752695431365823276953 1026564521573524367457715)
              ·
                refine ⟨1539846782360286551186573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1026564521573524367457715 1539846782360286551186573)
                ·
                  refine ⟨577442543385107456694965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1539846782360286551186573 577442543385107456694965)
                  ·
                    refine ⟨54135238442353824065153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 577442543385107456694965 54135238442353824065153)
                    ·
                      refine ⟨40601428831765368048865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54135238442353824065153 40601428831765368048865)
                      ·
                        rfl

theorem cell23_79071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_79071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79071 prefixEnd_79071 := by exact prefixLift 79071
  have htrace : WordTrace (prefixWord ++ tailWord_79071) baseStart_79071 baseEnd_79071 := by
    simpa [prefixWord, tailWord_79071, baseEnd_79071] using wordTrace_append hprefix tailTrace_79071
  have hstable : (prefixWord ++ tailWord_79071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79071).length < 2 ^ (prefixWord ++ tailWord_79071).sum := by decide
  have hdescent : baseEnd_79071 < baseStart_79071 := by decide
  rcases family_descends (prefixWord ++ tailWord_79071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79098 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_79098 : Nat := 118140960795 + 79098 * 2 ^ 59
def prefixEnd_79098 : Nat := 4983230072969 + 3 ^ 40 * 79098 * 2
def baseEnd_79098 : Nat := 13538430936478920803747

theorem tailTrace_79098 : CollatzResearch.WordTrace tailWord_79098 prefixEnd_79098 13538430936478920803747 := by
  unfold tailWord_79098
  simp only [CollatzResearch.WordTrace]
  refine ⟨721235266862232427003487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1923294044965953138675965 721235266862232427003487)
  ·
    refine ⟨1081852900293348640505231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721235266862232427003487 1081852900293348640505231)
    ·
      refine ⟨1622779350440022960757847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1081852900293348640505231 1622779350440022960757847)
      ·
        refine ⟨2434169025660034441136771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622779350440022960757847 2434169025660034441136771)
        ·
          refine ⟨3651253538490051661705157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434169025660034441136771 3651253538490051661705157)
          ·
            refine ⟨684610038466884686569717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3651253538490051661705157 684610038466884686569717)
            ·
              refine ⟨64182191106270439365911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 684610038466884686569717 64182191106270439365911)
              ·
                refine ⟨96273286659405659048867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64182191106270439365911 96273286659405659048867)
                ·
                  refine ⟨144409929989108488573301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96273286659405659048867 144409929989108488573301)
                  ·
                    refine ⟨13538430936478920803747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144409929989108488573301 13538430936478920803747)
                    ·
                      rfl

theorem cell23_79098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_79098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79098 prefixEnd_79098 := by exact prefixLift 79098
  have htrace : WordTrace (prefixWord ++ tailWord_79098) baseStart_79098 baseEnd_79098 := by
    simpa [prefixWord, tailWord_79098, baseEnd_79098] using wordTrace_append hprefix tailTrace_79098
  have hstable : (prefixWord ++ tailWord_79098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79098).length < 2 ^ (prefixWord ++ tailWord_79098).sum := by decide
  have hdescent : baseEnd_79098 < baseStart_79098 := by decide
  rcases family_descends (prefixWord ++ tailWord_79098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79106 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_79106 : Nat := 118140960795 + 79106 * 2 ^ 59
def prefixEnd_79106 : Nat := 4983230072969 + 3 ^ 40 * 79106 * 2
def baseEnd_79106 : Nat := 13539800218224243703735

theorem tailTrace_79106 : CollatzResearch.WordTrace tailWord_79106 prefixEnd_79106 13539800218224243703735 := by
  unfold tailWord_79106
  simp only [CollatzResearch.WordTrace]
  refine ⟨721308212854986768576293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1923488567613298049536781 721308212854986768576293)
  ·
    refine ⟨135245289910310019108055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 721308212854986768576293 135245289910310019108055)
    ·
      refine ⟨202867934865465028662083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135245289910310019108055 202867934865465028662083)
      ·
        refine ⟨304301902298197542993125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202867934865465028662083 304301902298197542993125)
        ·
          refine ⟨57056606680912039311211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304301902298197542993125 57056606680912039311211)
          ·
            refine ⟨85584910021368058966817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57056606680912039311211 85584910021368058966817)
            ·
              refine ⟨64188682516026044225113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85584910021368058966817 64188682516026044225113)
              ·
                refine ⟨48141511887019533168835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64188682516026044225113 48141511887019533168835)
                ·
                  refine ⟨72212267830529299753253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48141511887019533168835 72212267830529299753253)
                  ·
                    refine ⟨13539800218224243703735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72212267830529299753253 13539800218224243703735)
                    ·
                      rfl

theorem cell23_79106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_79106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79106 prefixEnd_79106 := by exact prefixLift 79106
  have htrace : WordTrace (prefixWord ++ tailWord_79106) baseStart_79106 baseEnd_79106 := by
    simpa [prefixWord, tailWord_79106, baseEnd_79106] using wordTrace_append hprefix tailTrace_79106
  have hstable : (prefixWord ++ tailWord_79106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79106).length < 2 ^ (prefixWord ++ tailWord_79106).sum := by decide
  have hdescent : baseEnd_79106 < baseStart_79106 := by decide
  rcases family_descends (prefixWord ++ tailWord_79106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79112 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_79112 : Nat := 118140960795 + 79112 * 2 ^ 59
def prefixEnd_79112 : Nat := 4983230072969 + 3 ^ 40 * 79112 * 2
def baseEnd_79112 : Nat := 40622481538599707636177

theorem tailTrace_79112 : CollatzResearch.WordTrace tailWord_79112 prefixEnd_79112 40622481538599707636177 := by
  unfold tailWord_79112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442725844699105049511795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1923634459598806732682393 1442725844699105049511795)
  ·
    refine ⟨2164088767048657574267693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1442725844699105049511795 2164088767048657574267693)
    ·
      refine ⟨811533287643246590350385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2164088767048657574267693 811533287643246590350385)
      ·
        refine ⟨608649965732434942762789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 811533287643246590350385 608649965732434942762789)
        ·
          refine ⟨114121868574831551768023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 608649965732434942762789 114121868574831551768023)
          ·
            refine ⟨171182802862247327652035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114121868574831551768023 171182802862247327652035)
            ·
              refine ⟨256774204293370991478053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171182802862247327652035 256774204293370991478053)
              ·
                refine ⟨48145163305007060902135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256774204293370991478053 48145163305007060902135)
                ·
                  refine ⟨72217744957510591353203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48145163305007060902135 72217744957510591353203)
                  ·
                    refine ⟨108326617436265887029805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72217744957510591353203 108326617436265887029805)
                    ·
                      refine ⟨40622481538599707636177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108326617436265887029805 40622481538599707636177)
                      ·
                        rfl

theorem cell23_79112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_79112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79112 prefixEnd_79112 := by exact prefixLift 79112
  have htrace : WordTrace (prefixWord ++ tailWord_79112) baseStart_79112 baseEnd_79112 := by
    simpa [prefixWord, tailWord_79112, baseEnd_79112] using wordTrace_append hprefix tailTrace_79112
  have hstable : (prefixWord ++ tailWord_79112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79112).length < 2 ^ (prefixWord ++ tailWord_79112).sum := by decide
  have hdescent : baseEnd_79112 < baseStart_79112 := by decide
  rcases family_descends (prefixWord ++ tailWord_79112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79121 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_79121 : Nat := 118140960795 + 79121 * 2 ^ 59
def prefixEnd_79121 : Nat := 4983230072969 + 3 ^ 40 * 79121 * 2
def baseEnd_79121 : Nat := 40627102864490172423635

theorem tailTrace_79121 : CollatzResearch.WordTrace tailWord_79121 prefixEnd_79121 40627102864490172423635 := by
  unfold tailWord_79121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885779946365604636101217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1923853297577069757400811 2885779946365604636101217)
  ·
    refine ⟨2164334959774203477075913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2885779946365604636101217 2164334959774203477075913)
    ·
      refine ⟨1623251219830652607806935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2164334959774203477075913 1623251219830652607806935)
      ·
        refine ⟨2434876829745978911710403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623251219830652607806935 2434876829745978911710403)
        ·
          refine ⟨3652315244618968367565605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434876829745978911710403 3652315244618968367565605)
          ·
            refine ⟨684809108366056568918551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3652315244618968367565605 684809108366056568918551)
            ·
              refine ⟨1027213662549084853377827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684809108366056568918551 1027213662549084853377827)
              ·
                refine ⟨1540820493823627280066741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027213662549084853377827 1540820493823627280066741)
                ·
                  refine ⟨144451921295965057506257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1540820493823627280066741 144451921295965057506257)
                  ·
                    refine ⟨108338940971973793129693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144451921295965057506257 108338940971973793129693)
                    ·
                      refine ⟨40627102864490172423635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108338940971973793129693 40627102864490172423635)
                      ·
                        rfl

theorem cell23_79121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_79121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79121 prefixEnd_79121 := by exact prefixLift 79121
  have htrace : WordTrace (prefixWord ++ tailWord_79121) baseStart_79121 baseEnd_79121 := by
    simpa [prefixWord, tailWord_79121, baseEnd_79121] using wordTrace_append hprefix tailTrace_79121
  have hstable : (prefixWord ++ tailWord_79121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79121).length < 2 ^ (prefixWord ++ tailWord_79121).sum := by decide
  have hdescent : baseEnd_79121 < baseStart_79121 := by decide
  rcases family_descends (prefixWord ++ tailWord_79121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79128 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 2, 4]
def baseStart_79128 : Nat := 118140960795 + 79128 * 2 ^ 59
def prefixEnd_79128 : Nat := 4983230072969 + 3 ^ 40 * 79128 * 2
def baseEnd_79128 : Nat := 13543565743023881678701

theorem tailTrace_79128 : CollatzResearch.WordTrace tailWord_79128 prefixEnd_79128 13543565743023881678701 := by
  unfold tailWord_79128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443017628670122415803019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1924023504893496554404025 1443017628670122415803019)
  ·
    refine ⟨2164526443005183623704529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1443017628670122415803019 2164526443005183623704529)
    ·
      refine ⟨1623394832253887717778397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2164526443005183623704529 1623394832253887717778397)
      ·
        refine ⟨608773062095207894166899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1623394832253887717778397 608773062095207894166899)
        ·
          refine ⟨913159593142811841250349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608773062095207894166899 913159593142811841250349)
          ·
            refine ⟨342434847428554440468881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 913159593142811841250349 342434847428554440468881)
            ·
              refine ⟨256826135571415830351661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342434847428554440468881 256826135571415830351661)
              ·
                refine ⟨96309800839280936381873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256826135571415830351661 96309800839280936381873)
                ·
                  refine ⟨72232350629460702286405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96309800839280936381873 72232350629460702286405)
                  ·
                    refine ⟨13543565743023881678701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72232350629460702286405 13543565743023881678701)
                    ·
                      rfl

theorem cell23_79128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_79128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79128 prefixEnd_79128 := by exact prefixLift 79128
  have htrace : WordTrace (prefixWord ++ tailWord_79128) baseStart_79128 baseEnd_79128 := by
    simpa [prefixWord, tailWord_79128, baseEnd_79128] using wordTrace_append hprefix tailTrace_79128
  have hstable : (prefixWord ++ tailWord_79128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79128).length < 2 ^ (prefixWord ++ tailWord_79128).sum := by decide
  have hdescent : baseEnd_79128 < baseStart_79128 := by decide
  rcases family_descends (prefixWord ++ tailWord_79128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79152 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 1, 2, 2]
def baseStart_79152 : Nat := 118140960795 + 79152 * 2 ^ 59
def prefixEnd_79152 : Nat := 4983230072969 + 3 ^ 40 * 79152 * 2
def baseEnd_79152 : Nat := 40643020764779551135993

theorem tailTrace_79152 : CollatzResearch.WordTrace tailWord_79152 prefixEnd_79152 40643020764779551135993 := by
  unfold tailWord_79152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443455304626648465239855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1924607072835531286986473 1443455304626648465239855)
  ·
    refine ⟨2165182956939972697859783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1443455304626648465239855 2165182956939972697859783)
    ·
      refine ⟨3247774435409959046789675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2165182956939972697859783 3247774435409959046789675)
      ·
        refine ⟨4871661653114938570184513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247774435409959046789675 4871661653114938570184513)
        ·
          refine ⟨3653746239836203927638385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871661653114938570184513 3653746239836203927638385)
          ·
            refine ⟨2740309679877152945728789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3653746239836203927638385 2740309679877152945728789)
            ·
              refine ⟨128452016244241544331037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2740309679877152945728789 128452016244241544331037)
              ·
                refine ⟨48169506091590579124139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128452016244241544331037 48169506091590579124139)
                ·
                  refine ⟨72254259137385868686209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48169506091590579124139 72254259137385868686209)
                  ·
                    refine ⟨54190694353039401514657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72254259137385868686209 54190694353039401514657)
                    ·
                      refine ⟨40643020764779551135993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54190694353039401514657 40643020764779551135993)
                      ·
                        rfl

theorem cell23_79152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 2, 2].length) (baseStart_79152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79152 prefixEnd_79152 := by exact prefixLift 79152
  have htrace : WordTrace (prefixWord ++ tailWord_79152) baseStart_79152 baseEnd_79152 := by
    simpa [prefixWord, tailWord_79152, baseEnd_79152] using wordTrace_append hprefix tailTrace_79152
  have hstable : (prefixWord ++ tailWord_79152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79152).length < 2 ^ (prefixWord ++ tailWord_79152).sum := by decide
  have hdescent : baseEnd_79152 < baseStart_79152 := by decide
  rcases family_descends (prefixWord ++ tailWord_79152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79155 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 1, 2, 3]
def baseStart_79155 : Nat := 118140960795 + 79155 * 2 ^ 59
def prefixEnd_79155 : Nat := 4983230072969 + 3 ^ 40 * 79155 * 2
def baseEnd_79155 : Nat := 40644561206743039398479

theorem tailTrace_79155 : CollatzResearch.WordTrace tailWord_79155 prefixEnd_79155 40644561206743039398479 := by
  unfold tailWord_79155
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887020028242428442838919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1924680018828285628559279 2887020028242428442838919)
  ·
    refine ⟨4330530042363642664258379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2887020028242428442838919 4330530042363642664258379)
    ·
      refine ⟨6495795063545463996387569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4330530042363642664258379 6495795063545463996387569)
      ·
        refine ⟨4871846297659097997290677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6495795063545463996387569 4871846297659097997290677)
        ·
          refine ⟨456735590405540437246001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4871846297659097997290677 456735590405540437246001)
          ·
            refine ⟨342551692804155327934501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456735590405540437246001 342551692804155327934501)
            ·
              refine ⟨64228442400779123987719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 342551692804155327934501 64228442400779123987719)
              ·
                refine ⟨96342663601168685981579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64228442400779123987719 96342663601168685981579)
                ·
                  refine ⟨144513995401753028972369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96342663601168685981579 144513995401753028972369)
                  ·
                    refine ⟨108385496551314771729277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144513995401753028972369 108385496551314771729277)
                    ·
                      refine ⟨40644561206743039398479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108385496551314771729277 40644561206743039398479)
                      ·
                        rfl

theorem cell23_79155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 2, 3].length) (baseStart_79155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79155 prefixEnd_79155 := by exact prefixLift 79155
  have htrace : WordTrace (prefixWord ++ tailWord_79155) baseStart_79155 baseEnd_79155 := by
    simpa [prefixWord, tailWord_79155, baseEnd_79155] using wordTrace_append hprefix tailTrace_79155
  have hstable : (prefixWord ++ tailWord_79155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79155).length < 2 ^ (prefixWord ++ tailWord_79155).sum := by decide
  have hdescent : baseEnd_79155 < baseStart_79155 := by decide
  rcases family_descends (prefixWord ++ tailWord_79155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79168 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 4, 1, 3]
def baseStart_79168 : Nat := 118140960795 + 79168 * 2 ^ 59
def prefixEnd_79168 : Nat := 4983230072969 + 3 ^ 40 * 79168 * 2
def baseEnd_79168 : Nat := 40651236455251488535919

theorem tailTrace_79168 : CollatzResearch.WordTrace tailWord_79168 prefixEnd_79168 40651236455251488535919 := by
  unfold tailWord_79168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443747088597665831531079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1924996118130221108708105 1443747088597665831531079)
  ·
    refine ⟨2165620632896498747296619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1443747088597665831531079 2165620632896498747296619)
    ·
      refine ⟨3248430949344748120944929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2165620632896498747296619 3248430949344748120944929)
      ·
        refine ⟨2436323212008561090708697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3248430949344748120944929 2436323212008561090708697)
        ·
          refine ⟨1827242409006420818031523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436323212008561090708697 1827242409006420818031523)
          ·
            refine ⟨2740863613509631227047285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827242409006420818031523 2740863613509631227047285)
            ·
              refine ⟨256955963766527927535683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2740863613509631227047285 256955963766527927535683)
              ·
                refine ⟨385433945649791891303525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256955963766527927535683 385433945649791891303525)
                ·
                  refine ⟨72268864809335979619411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385433945649791891303525 72268864809335979619411)
                  ·
                    refine ⟨108403297214003969429117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72268864809335979619411 108403297214003969429117)
                    ·
                      refine ⟨40651236455251488535919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108403297214003969429117 40651236455251488535919)
                      ·
                        rfl

theorem cell23_79168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_79168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79168 prefixEnd_79168 := by exact prefixLift 79168
  have htrace : WordTrace (prefixWord ++ tailWord_79168) baseStart_79168 baseEnd_79168 := by
    simpa [prefixWord, tailWord_79168, baseEnd_79168] using wordTrace_append hprefix tailTrace_79168
  have hstable : (prefixWord ++ tailWord_79168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79168).length < 2 ^ (prefixWord ++ tailWord_79168).sum := by decide
  have hdescent : baseEnd_79168 < baseStart_79168 := by decide
  rcases family_descends (prefixWord ++ tailWord_79168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79169 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_79169 : Nat := 118140960795 + 79169 * 2 ^ 59
def prefixEnd_79169 : Nat := 4983230072969 + 3 ^ 40 * 79169 * 2
def baseEnd_79169 : Nat := 40651749935905984623415

theorem tailTrace_79169 : CollatzResearch.WordTrace tailWord_79169 prefixEnd_79169 40651749935905984623415 := by
  unfold tailWord_79169
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887530650191708833848561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1925020433461139222565707 2887530650191708833848561)
  ·
    refine ⟨2165647987643781625386421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2887530650191708833848561 2165647987643781625386421)
    ·
      refine ⟨203029498841604527379977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2165647987643781625386421 203029498841604527379977)
      ·
        refine ⟨152272124131203395534983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203029498841604527379977 152272124131203395534983)
        ·
          refine ⟨228408186196805093302475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152272124131203395534983 228408186196805093302475)
          ·
            refine ⟨342612279295207639953713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228408186196805093302475 342612279295207639953713)
            ·
              refine ⟨256959209471405729965285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342612279295207639953713 256959209471405729965285)
              ·
                refine ⟨48179851775888574368491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256959209471405729965285 48179851775888574368491)
                ·
                  refine ⟨72269777663832861552737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48179851775888574368491 72269777663832861552737)
                  ·
                    refine ⟨54202333247874646164553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72269777663832861552737 54202333247874646164553)
                    ·
                      refine ⟨40651749935905984623415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54202333247874646164553 40651749935905984623415)
                      ·
                        rfl

theorem cell23_79169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_79169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79169 prefixEnd_79169 := by exact prefixLift 79169
  have htrace : WordTrace (prefixWord ++ tailWord_79169) baseStart_79169 baseEnd_79169 := by
    simpa [prefixWord, tailWord_79169, baseEnd_79169] using wordTrace_append hprefix tailTrace_79169
  have hstable : (prefixWord ++ tailWord_79169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79169).length < 2 ^ (prefixWord ++ tailWord_79169).sum := by decide
  have hdescent : baseEnd_79169 < baseStart_79169 := by decide
  rcases family_descends (prefixWord ++ tailWord_79169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79178 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_79178 : Nat := 118140960795 + 79178 * 2 ^ 59
def prefixEnd_79178 : Nat := 4983230072969 + 3 ^ 40 * 79178 * 2
def baseEnd_79178 : Nat := 40656371261796449410873

theorem tailTrace_79178 : CollatzResearch.WordTrace tailWord_79178 prefixEnd_79178 40656371261796449410873 := by
  unfold tailWord_79178
  simp only [CollatzResearch.WordTrace]
  refine ⟨721964726789775842731547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1925239271439402247284125 721964726789775842731547)
  ·
    refine ⟨1082947090184663764097321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721964726789775842731547 1082947090184663764097321)
    ·
      refine ⟨812210317638497823072991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1082947090184663764097321 812210317638497823072991)
      ·
        refine ⟨1218315476457746734609487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812210317638497823072991 1218315476457746734609487)
        ·
          refine ⟨1827473214686620101914231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218315476457746734609487 1827473214686620101914231)
          ·
            refine ⟨2741209822029930152871347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827473214686620101914231 2741209822029930152871347)
            ·
              refine ⟨4111814733044895229307021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741209822029930152871347 4111814733044895229307021)
              ·
                refine ⟨1541930524891835710990133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4111814733044895229307021 1541930524891835710990133)
                ·
                  refine ⟨144555986708609597905325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1541930524891835710990133 144555986708609597905325)
                  ·
                    refine ⟨54208495015728599214497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144555986708609597905325 54208495015728599214497)
                    ·
                      refine ⟨40656371261796449410873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54208495015728599214497 40656371261796449410873)
                      ·
                        rfl

theorem cell23_79178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_79178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79178 prefixEnd_79178 := by exact prefixLift 79178
  have htrace : WordTrace (prefixWord ++ tailWord_79178) baseStart_79178 baseEnd_79178 := by
    simpa [prefixWord, tailWord_79178, baseEnd_79178] using wordTrace_append hprefix tailTrace_79178
  have hstable : (prefixWord ++ tailWord_79178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79178).length < 2 ^ (prefixWord ++ tailWord_79178).sum := by decide
  have hdescent : baseEnd_79178 < baseStart_79178 := by decide
  rcases family_descends (prefixWord ++ tailWord_79178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79225 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 4, 2, 2]
def baseStart_79225 : Nat := 118140960795 + 79225 * 2 ^ 59
def prefixEnd_79225 : Nat := 4983230072969 + 3 ^ 40 * 79225 * 2
def baseEnd_79225 : Nat := 40680504852557765523157

theorem tailTrace_79225 : CollatzResearch.WordTrace tailWord_79225 prefixEnd_79225 40680504852557765523157 := by
  unfold tailWord_79225
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889573137988830397887129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1926382091992553598591419 2889573137988830397887129)
  ·
    refine ⟨2167179853491622798415347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2889573137988830397887129 2167179853491622798415347)
    ·
      refine ⟨3250769780237434197623021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167179853491622798415347 3250769780237434197623021)
      ·
        refine ⟨1219038667589037824108633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3250769780237434197623021 1219038667589037824108633)
        ·
          refine ⟨914279000691778368081475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219038667589037824108633 914279000691778368081475)
          ·
            refine ⟨1371418501037667552122213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914279000691778368081475 1371418501037667552122213)
            ·
              refine ⟨257140968944562666022915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1371418501037667552122213 257140968944562666022915)
              ·
                refine ⟨385711453416843999034373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257140968944562666022915 385711453416843999034373)
                ·
                  refine ⟨72320897515658249818945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 385711453416843999034373 72320897515658249818945)
                  ·
                    refine ⟨54240673136743687364209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72320897515658249818945 54240673136743687364209)
                    ·
                      refine ⟨40680504852557765523157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54240673136743687364209 40680504852557765523157)
                      ·
                        rfl

theorem cell23_79225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_79225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79225 prefixEnd_79225 := by exact prefixLift 79225
  have htrace : WordTrace (prefixWord ++ tailWord_79225) baseStart_79225 baseEnd_79225 := by
    simpa [prefixWord, tailWord_79225, baseEnd_79225] using wordTrace_append hprefix tailTrace_79225
  have hstable : (prefixWord ++ tailWord_79225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79225).length < 2 ^ (prefixWord ++ tailWord_79225).sum := by decide
  have hdescent : baseEnd_79225 < baseStart_79225 := by decide
  rcases family_descends (prefixWord ++ tailWord_79225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79246 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_79246 : Nat := 118140960795 + 79246 * 2 ^ 59
def prefixEnd_79246 : Nat := 4983230072969 + 3 ^ 40 * 79246 * 2
def baseEnd_79246 : Nat := 40691287946302183360561

theorem tailTrace_79246 : CollatzResearch.WordTrace tailWord_79246 prefixEnd_79246 40691287946302183360561 := by
  unfold tailWord_79246
  simp only [CollatzResearch.WordTrace]
  refine ⟨361292383864093873050199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1926892713941833989601061 361292383864093873050199)
  ·
    refine ⟨541938575796140809575299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361292383864093873050199 541938575796140809575299)
    ·
      refine ⟨812907863694211214362949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541938575796140809575299 812907863694211214362949)
      ·
        refine ⟨152420224442664602693053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 812907863694211214362949 152420224442664602693053)
        ·
          refine ⟨57157584165999226009895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152420224442664602693053 57157584165999226009895)
          ·
            refine ⟨85736376248998839014843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57157584165999226009895 85736376248998839014843)
            ·
              refine ⟨128604564373498258522265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85736376248998839014843 128604564373498258522265)
              ·
                refine ⟨96453423280123693891699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128604564373498258522265 96453423280123693891699)
                ·
                  refine ⟨144680134920185540837549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96453423280123693891699 144680134920185540837549)
                  ·
                    refine ⟨54255050595069577814081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144680134920185540837549 54255050595069577814081)
                    ·
                      refine ⟨40691287946302183360561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54255050595069577814081 40691287946302183360561)
                      ·
                        rfl

theorem cell23_79246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_79246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79246 prefixEnd_79246 := by exact prefixLift 79246
  have htrace : WordTrace (prefixWord ++ tailWord_79246) baseStart_79246 baseEnd_79246 := by
    simpa [prefixWord, tailWord_79246, baseEnd_79246] using wordTrace_append hprefix tailTrace_79246
  have hstable : (prefixWord ++ tailWord_79246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79246).length < 2 ^ (prefixWord ++ tailWord_79246).sum := by decide
  have hdescent : baseEnd_79246 < baseStart_79246 := by decide
  rcases family_descends (prefixWord ++ tailWord_79246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79285 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_79285 : Nat := 118140960795 + 79285 * 2 ^ 59
def prefixEnd_79285 : Nat := 4983230072969 + 3 ^ 40 * 79285 * 2
def baseEnd_79285 : Nat := 40711313691827530772881

theorem tailTrace_79285 : CollatzResearch.WordTrace tailWord_79285 prefixEnd_79285 40711313691827530772881 := by
  unfold tailWord_79285
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891761517771460645071309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1927841011847640430047539 2891761517771460645071309)
  ·
    refine ⟨1084410569164297741901741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2891761517771460645071309 1084410569164297741901741)
    ·
      refine ⟨406653963436611653213153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1084410569164297741901741 406653963436611653213153)
      ·
        refine ⟨304990472577458739909865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406653963436611653213153 304990472577458739909865)
        ·
          refine ⟨228742854433094054932399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304990472577458739909865 228742854433094054932399)
          ·
            refine ⟨343114281649641082398599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228742854433094054932399 343114281649641082398599)
            ·
              refine ⟨514671422474461623597899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343114281649641082398599 514671422474461623597899)
              ·
                refine ⟨772007133711692435396849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514671422474461623597899 772007133711692435396849)
                ·
                  refine ⟨579005350283769326547637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772007133711692435396849 579005350283769326547637)
                  ·
                    refine ⟨54281751589103374363841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 579005350283769326547637 54281751589103374363841)
                    ·
                      refine ⟨40711313691827530772881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54281751589103374363841 40711313691827530772881)
                      ·
                        rfl

theorem cell23_79285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_79285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79285 prefixEnd_79285 := by exact prefixLift 79285
  have htrace : WordTrace (prefixWord ++ tailWord_79285) baseStart_79285 baseEnd_79285 := by
    simpa [prefixWord, tailWord_79285, baseEnd_79285] using wordTrace_append hprefix tailTrace_79285
  have hstable : (prefixWord ++ tailWord_79285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79285).length < 2 ^ (prefixWord ++ tailWord_79285).sum := by decide
  have hdescent : baseEnd_79285 < baseStart_79285 := by decide
  rcases family_descends (prefixWord ++ tailWord_79285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79342 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_79342 : Nat := 118140960795 + 79342 * 2 ^ 59
def prefixEnd_79342 : Nat := 4983230072969 + 3 ^ 40 * 79342 * 2
def baseEnd_79342 : Nat := 13580194029711269253373

theorem tailTrace_79342 : CollatzResearch.WordTrace tailWord_79342 prefixEnd_79342 13580194029711269253373 := by
  unfold tailWord_79342
  simp only [CollatzResearch.WordTrace]
  refine ⟨361730059820619922487035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1929226985709972919930853 361730059820619922487035)
  ·
    refine ⟨542595089730929883730553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361730059820619922487035 542595089730929883730553)
    ·
      refine ⟨406946317298197412797915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542595089730929883730553 406946317298197412797915)
      ·
        refine ⟨610419475947296119196873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406946317298197412797915 610419475947296119196873)
        ·
          refine ⟨457814606960472089397655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610419475947296119196873 457814606960472089397655)
          ·
            refine ⟨686721910440708134096483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457814606960472089397655 686721910440708134096483)
            ·
              refine ⟨1030082865661062201144725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686721910440708134096483 1030082865661062201144725)
              ·
                refine ⟨48285134327862290678659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1030082865661062201144725 48285134327862290678659)
                ·
                  refine ⟨72427701491793436017989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48285134327862290678659 72427701491793436017989)
                  ·
                    refine ⟨13580194029711269253373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72427701491793436017989 13580194029711269253373)
                    ·
                      rfl

theorem cell23_79342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_79342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79342 prefixEnd_79342 := by exact prefixLift 79342
  have htrace : WordTrace (prefixWord ++ tailWord_79342) baseStart_79342 baseEnd_79342 := by
    simpa [prefixWord, tailWord_79342, baseEnd_79342] using wordTrace_append hprefix tailTrace_79342
  have hstable : (prefixWord ++ tailWord_79342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79342).length < 2 ^ (prefixWord ++ tailWord_79342).sum := by decide
  have hdescent : baseEnd_79342 < baseStart_79342 := by decide
  rcases family_descends (prefixWord ++ tailWord_79342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79351 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 9]
def baseStart_79351 : Nat := 118140960795 + 79351 * 2 ^ 59
def prefixEnd_79351 : Nat := 4983230072969 + 3 ^ 40 * 79351 * 2
def baseEnd_79351 : Nat := 13581734471674757515859

theorem tailTrace_79351 : CollatzResearch.WordTrace tailWord_79351 prefixEnd_79351 13581734471674757515859 := by
  unfold tailWord_79351
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894168735532353916973907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929445823688235944649271 2894168735532353916973907)
  ·
    refine ⟨4341253103298530875460861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2894168735532353916973907 4341253103298530875460861)
    ·
      refine ⟨1627969913736949078297823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4341253103298530875460861 1627969913736949078297823)
      ·
        refine ⟨2441954870605423617446735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627969913736949078297823 2441954870605423617446735)
        ·
          refine ⟨3662932305908135426170103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441954870605423617446735 3662932305908135426170103)
          ·
            refine ⟨5494398458862203139255155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662932305908135426170103 5494398458862203139255155)
            ·
              refine ⟨8241597688293304708882733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494398458862203139255155 8241597688293304708882733)
              ·
                refine ⟨3090599133109989265831025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8241597688293304708882733 3090599133109989265831025)
                ·
                  refine ⟨2317949349832491949373269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090599133109989265831025 2317949349832491949373269)
                  ·
                    refine ⟨13581734471674757515859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2317949349832491949373269 13581734471674757515859)
                    ·
                      rfl

theorem cell23_79351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_79351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79351 prefixEnd_79351 := by exact prefixLift 79351
  have htrace : WordTrace (prefixWord ++ tailWord_79351) baseStart_79351 baseEnd_79351 := by
    simpa [prefixWord, tailWord_79351, baseEnd_79351] using wordTrace_append hprefix tailTrace_79351
  have hstable : (prefixWord ++ tailWord_79351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79351).length < 2 ^ (prefixWord ++ tailWord_79351).sum := by decide
  have hdescent : baseEnd_79351 < baseStart_79351 := by decide
  rcases family_descends (prefixWord ++ tailWord_79351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79368 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_79368 : Nat := 118140960795 + 79368 * 2 ^ 59
def prefixEnd_79368 : Nat := 4983230072969 + 3 ^ 40 * 79368 * 2
def baseEnd_79368 : Nat := 13584644195383568678333

theorem tailTrace_79368 : CollatzResearch.WordTrace tailWord_79368 prefixEnd_79368 13584644195383568678333 := by
  unfold tailWord_79368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447394388235382910171379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1929859184313843880228505 1447394388235382910171379)
  ·
    refine ⟨2171091582353074365257069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1447394388235382910171379 2171091582353074365257069)
    ·
      refine ⟨814159343382402886971401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2171091582353074365257069 814159343382402886971401)
      ·
        refine ⟨610619507536802165228551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814159343382402886971401 610619507536802165228551)
        ·
          refine ⟨915929261305203247842827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610619507536802165228551 915929261305203247842827)
          ·
            refine ⟨1373893891957804871764241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915929261305203247842827 1373893891957804871764241)
            ·
              refine ⟨1030420418968353653823181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373893891957804871764241 1030420418968353653823181)
              ·
                refine ⟨386407657113132620183693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1030420418968353653823181 386407657113132620183693)
                ·
                  refine ⟨144902871417424732568885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386407657113132620183693 144902871417424732568885)
                  ·
                    refine ⟨13584644195383568678333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 144902871417424732568885 13584644195383568678333)
                    ·
                      rfl

theorem cell23_79368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_79368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79368 prefixEnd_79368 := by exact prefixLift 79368
  have htrace : WordTrace (prefixWord ++ tailWord_79368) baseStart_79368 baseEnd_79368 := by
    simpa [prefixWord, tailWord_79368, baseEnd_79368] using wordTrace_append hprefix tailTrace_79368
  have hstable : (prefixWord ++ tailWord_79368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79368).length < 2 ^ (prefixWord ++ tailWord_79368).sum := by decide
  have hdescent : baseEnd_79368 < baseStart_79368 := by decide
  rcases family_descends (prefixWord ++ tailWord_79368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79392 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 4, 3, 2]
def baseStart_79392 : Nat := 118140960795 + 79392 * 2 ^ 59
def prefixEnd_79392 : Nat := 4983230072969 + 3 ^ 40 * 79392 * 2
def baseEnd_79392 : Nat := 40766256121858612134889

theorem tailTrace_79392 : CollatzResearch.WordTrace tailWord_79392 prefixEnd_79392 40766256121858612134889 := by
  unfold tailWord_79392
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447832064191908959608215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1930442752255878612810953 1447832064191908959608215)
  ·
    refine ⟨2171748096287863439412323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1447832064191908959608215 2171748096287863439412323)
    ·
      refine ⟨3257622144431795159118485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171748096287863439412323 3257622144431795159118485)
      ·
        refine ⟨152701038020240398083679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3257622144431795159118485 152701038020240398083679)
        ·
          refine ⟨229051557030360597125519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152701038020240398083679 229051557030360597125519)
          ·
            refine ⟨343577335545540895688279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229051557030360597125519 343577335545540895688279)
            ·
              refine ⟨515366003318311343532419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343577335545540895688279 515366003318311343532419)
              ·
                refine ⟨773049004977467015298629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515366003318311343532419 773049004977467015298629)
                ·
                  refine ⟨144946688433275065368493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 773049004977467015298629 144946688433275065368493)
                  ·
                    refine ⟨54355008162478149513185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144946688433275065368493 54355008162478149513185)
                    ·
                      refine ⟨40766256121858612134889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54355008162478149513185 40766256121858612134889)
                      ·
                        rfl

theorem cell23_79392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_79392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79392 prefixEnd_79392 := by exact prefixLift 79392
  have htrace : WordTrace (prefixWord ++ tailWord_79392) baseStart_79392 baseEnd_79392 := by
    simpa [prefixWord, tailWord_79392, baseEnd_79392] using wordTrace_append hprefix tailTrace_79392
  have hstable : (prefixWord ++ tailWord_79392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79392).length < 2 ^ (prefixWord ++ tailWord_79392).sum := by decide
  have hdescent : baseEnd_79392 < baseStart_79392 := by decide
  rcases family_descends (prefixWord ++ tailWord_79392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79408 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_79408 : Nat := 118140960795 + 79408 * 2 ^ 59
def prefixEnd_79408 : Nat := 4983230072969 + 3 ^ 40 * 79408 * 2
def baseEnd_79408 : Nat := 40774471812330549534815

theorem tailTrace_79408 : CollatzResearch.WordTrace tailWord_79408 prefixEnd_79408 40774471812330549534815 := by
  unfold tailWord_79408
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448123848162926325899439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1930831797550568434532585 1448123848162926325899439)
  ·
    refine ⟨2172185772244389488849159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1448123848162926325899439 2172185772244389488849159)
    ·
      refine ⟨3258278658366584233273739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172185772244389488849159 3258278658366584233273739)
      ·
        refine ⟨4887417987549876349910609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258278658366584233273739 4887417987549876349910609)
        ·
          refine ⟨3665563490662407262432957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4887417987549876349910609 3665563490662407262432957)
          ·
            refine ⟨1374586308998402723412359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3665563490662407262432957 1374586308998402723412359)
            ·
              refine ⟨2061879463497604085118539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374586308998402723412359 2061879463497604085118539)
              ·
                refine ⟨3092819195246406127677809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061879463497604085118539 3092819195246406127677809)
                ·
                  refine ⟨2319614396434804595758357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092819195246406127677809 2319614396434804595758357)
                  ·
                    refine ⟨108731924832881465426173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2319614396434804595758357 108731924832881465426173)
                    ·
                      refine ⟨40774471812330549534815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108731924832881465426173 40774471812330549534815)
                      ·
                        rfl

theorem cell23_79408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_79408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79408 prefixEnd_79408 := by exact prefixLift 79408
  have htrace : WordTrace (prefixWord ++ tailWord_79408) baseStart_79408 baseEnd_79408 := by
    simpa [prefixWord, tailWord_79408, baseEnd_79408] using wordTrace_append hprefix tailTrace_79408
  have hstable : (prefixWord ++ tailWord_79408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79408).length < 2 ^ (prefixWord ++ tailWord_79408).sum := by decide
  have hdescent : baseEnd_79408 < baseStart_79408 := by decide
  rcases family_descends (prefixWord ++ tailWord_79408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79418 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_79418 : Nat := 118140960795 + 79418 * 2 ^ 59
def prefixEnd_79418 : Nat := 4983230072969 + 3 ^ 40 * 79418 * 2
def baseEnd_79418 : Nat := 40779606618875510409769

theorem tailTrace_79418 : CollatzResearch.WordTrace tailWord_79418 prefixEnd_79418 40779606618875510409769 := by
  unfold tailWord_79418
  simp only [CollatzResearch.WordTrace]
  refine ⟨724153106572406089915727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1931074950859749573108605 724153106572406089915727)
  ·
    refine ⟨1086229659858609134873591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724153106572406089915727 1086229659858609134873591)
    ·
      refine ⟨1629344489787913702310387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086229659858609134873591 1629344489787913702310387)
      ·
        refine ⟨2444016734681870553465581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629344489787913702310387 2444016734681870553465581)
        ·
          refine ⟨916506275505701457549593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2444016734681870553465581 916506275505701457549593)
          ·
            refine ⟨687379706629276093162195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916506275505701457549593 687379706629276093162195)
            ·
              refine ⟨1031069559943914139743293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687379706629276093162195 1031069559943914139743293)
              ·
                refine ⟨386651084978967802403735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1031069559943914139743293 386651084978967802403735)
                ·
                  refine ⟨579976627468451703605603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386651084978967802403735 579976627468451703605603)
                  ·
                    refine ⟨869964941202677555408405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579976627468451703605603 869964941202677555408405)
                    ·
                      refine ⟨40779606618875510409769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 869964941202677555408405 40779606618875510409769)
                      ·
                        rfl

theorem cell23_79418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_79418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79418 prefixEnd_79418 := by exact prefixLift 79418
  have htrace : WordTrace (prefixWord ++ tailWord_79418) baseStart_79418 baseEnd_79418 := by
    simpa [prefixWord, tailWord_79418, baseEnd_79418] using wordTrace_append hprefix tailTrace_79418
  have hstable : (prefixWord ++ tailWord_79418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79418).length < 2 ^ (prefixWord ++ tailWord_79418).sum := by decide
  have hdescent : baseEnd_79418 < baseStart_79418 := by decide
  rcases family_descends (prefixWord ++ tailWord_79418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79439 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 1, 2, 2]
def baseStart_79439 : Nat := 118140960795 + 79439 * 2 ^ 59
def prefixEnd_79439 : Nat := 4983230072969 + 3 ^ 40 * 79439 * 2
def baseEnd_79439 : Nat := 40790389712619928247173

theorem tailTrace_79439 : CollatzResearch.WordTrace tailWord_79439 prefixEnd_79439 40790389712619928247173 := by
  unfold tailWord_79439
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897378359213544946177371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1931585572809029964118247 2897378359213544946177371)
  ·
    refine ⟨4346067538820317419266057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2897378359213544946177371 4346067538820317419266057)
    ·
      refine ⟨3259550654115238064449543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4346067538820317419266057 3259550654115238064449543)
      ·
        refine ⟨4889325981172857096674315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259550654115238064449543 4889325981172857096674315)
        ·
          refine ⟨7333988971759285645011473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889325981172857096674315 7333988971759285645011473)
          ·
            refine ⟨5500491728819464233758605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7333988971759285645011473 5500491728819464233758605)
            ·
              refine ⟨2062684398307299087659477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5500491728819464233758605 2062684398307299087659477)
              ·
                refine ⟨48344165585327322367019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2062684398307299087659477 48344165585327322367019)
                ·
                  refine ⟨72516248377990983550529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48344165585327322367019 72516248377990983550529)
                  ·
                    refine ⟨54387186283493237662897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72516248377990983550529 54387186283493237662897)
                    ·
                      refine ⟨40790389712619928247173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54387186283493237662897 40790389712619928247173)
                      ·
                        rfl

theorem cell23_79439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 2, 2].length) (baseStart_79439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79439 prefixEnd_79439 := by exact prefixLift 79439
  have htrace : WordTrace (prefixWord ++ tailWord_79439) baseStart_79439 baseEnd_79439 := by
    simpa [prefixWord, tailWord_79439, baseEnd_79439] using wordTrace_append hprefix tailTrace_79439
  have hstable : (prefixWord ++ tailWord_79439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79439).length < 2 ^ (prefixWord ++ tailWord_79439).sum := by decide
  have hdescent : baseEnd_79439 < baseStart_79439 := by decide
  rcases family_descends (prefixWord ++ tailWord_79439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79442 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_79442 : Nat := 118140960795 + 79442 * 2 ^ 59
def prefixEnd_79442 : Nat := 4983230072969 + 3 ^ 40 * 79442 * 2
def baseEnd_79442 : Nat := 40791930154583416509659

theorem tailTrace_79442 : CollatzResearch.WordTrace tailWord_79442 prefixEnd_79442 40791930154583416509659 := by
  unfold tailWord_79442
  simp only [CollatzResearch.WordTrace]
  refine ⟨724371944550669114634145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1931658518801784305691053 724371944550669114634145)
  ·
    refine ⟨543278958413001835975609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 724371944550669114634145 543278958413001835975609)
    ·
      refine ⟨407459218809751376981707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 543278958413001835975609 407459218809751376981707)
      ·
        refine ⟨611188828214627065472561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407459218809751376981707 611188828214627065472561)
        ·
          refine ⟨458391621160970299104421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611188828214627065472561 458391621160970299104421)
          ·
            refine ⟨85948428967681931082079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 458391621160970299104421 85948428967681931082079)
            ·
              refine ⟨128922643451522896623119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85948428967681931082079 128922643451522896623119)
              ·
                refine ⟨193383965177284344934679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128922643451522896623119 193383965177284344934679)
                ·
                  refine ⟨290075947765926517402019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193383965177284344934679 290075947765926517402019)
                  ·
                    refine ⟨435113921648889776103029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 290075947765926517402019 435113921648889776103029)
                    ·
                      refine ⟨40791930154583416509659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 435113921648889776103029 40791930154583416509659)
                      ·
                        rfl

theorem cell23_79442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_79442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79442 prefixEnd_79442 := by exact prefixLift 79442
  have htrace : WordTrace (prefixWord ++ tailWord_79442) baseStart_79442 baseEnd_79442 := by
    simpa [prefixWord, tailWord_79442, baseEnd_79442] using wordTrace_append hprefix tailTrace_79442
  have hstable : (prefixWord ++ tailWord_79442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79442).length < 2 ^ (prefixWord ++ tailWord_79442).sum := by decide
  have hdescent : baseEnd_79442 < baseStart_79442 := by decide
  rcases family_descends (prefixWord ++ tailWord_79442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79468 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_79468 : Nat := 118140960795 + 79468 * 2 ^ 59
def prefixEnd_79468 : Nat := 4983230072969 + 3 ^ 40 * 79468 * 2
def baseEnd_79468 : Nat := 40805280651600314784539

theorem tailTrace_79468 : CollatzResearch.WordTrace tailWord_79468 prefixEnd_79468 40805280651600314784539 := by
  unfold tailWord_79468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449218038054241449491529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1932290717405655265988705 1449218038054241449491529)
  ·
    refine ⟨1086913528540681087118647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1449218038054241449491529 1086913528540681087118647)
    ·
      refine ⟨1630370292811021630677971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086913528540681087118647 1630370292811021630677971)
      ·
        refine ⟨2445555439216532446016957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630370292811021630677971 2445555439216532446016957)
        ·
          refine ⟨917083289706199667256359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2445555439216532446016957 917083289706199667256359)
          ·
            refine ⟨1375624934559299500884539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917083289706199667256359 1375624934559299500884539)
            ·
              refine ⟨2063437401838949251326809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375624934559299500884539 2063437401838949251326809)
              ·
                refine ⟨1547578051379211938495107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063437401838949251326809 1547578051379211938495107)
                ·
                  refine ⟨2321367077068817907742661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547578051379211938495107 2321367077068817907742661)
                  ·
                    refine ⟨435256326950403357701749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2321367077068817907742661 435256326950403357701749)
                    ·
                      refine ⟨40805280651600314784539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 435256326950403357701749 40805280651600314784539)
                      ·
                        rfl

theorem cell23_79468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_79468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79468 prefixEnd_79468 := by exact prefixLift 79468
  have htrace : WordTrace (prefixWord ++ tailWord_79468) baseStart_79468 baseEnd_79468 := by
    simpa [prefixWord, tailWord_79468, baseEnd_79468] using wordTrace_append hprefix tailTrace_79468
  have hstable : (prefixWord ++ tailWord_79468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79468).length < 2 ^ (prefixWord ++ tailWord_79468).sum := by decide
  have hdescent : baseEnd_79468 < baseStart_79468 := by decide
  rcases family_descends (prefixWord ++ tailWord_79468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79472 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_79472 : Nat := 118140960795 + 79472 * 2 ^ 59
def prefixEnd_79472 : Nat := 4983230072969 + 3 ^ 40 * 79472 * 2
def baseEnd_79472 : Nat := 40807334574218299134521

theorem tailTrace_79472 : CollatzResearch.WordTrace tailWord_79472 prefixEnd_79472 40807334574218299134521 := by
  unfold tailWord_79472
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449290984046995791064335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1932387978729327721419113 1449290984046995791064335)
  ·
    refine ⟨2173936476070493686596503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449290984046995791064335 2173936476070493686596503)
    ·
      refine ⟨3260904714105740529894755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173936476070493686596503 3260904714105740529894755)
      ·
        refine ⟨4891357071158610794842133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260904714105740529894755 4891357071158610794842133)
        ·
          refine ⟨229282362710559881008225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4891357071158610794842133 229282362710559881008225)
          ·
            refine ⟨171961772032919910756169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229282362710559881008225 171961772032919910756169)
            ·
              refine ⟨128971329024689933067127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171961772032919910756169 128971329024689933067127)
              ·
                refine ⟨193456993537034899600691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128971329024689933067127 193456993537034899600691)
                ·
                  refine ⟨290185490305552349401037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193456993537034899600691 290185490305552349401037)
                  ·
                    refine ⟨108819558864582131025389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290185490305552349401037 108819558864582131025389)
                    ·
                      refine ⟨40807334574218299134521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108819558864582131025389 40807334574218299134521)
                      ·
                        rfl

theorem cell23_79472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_79472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79472 prefixEnd_79472 := by exact prefixLift 79472
  have htrace : WordTrace (prefixWord ++ tailWord_79472) baseStart_79472 baseEnd_79472 := by
    simpa [prefixWord, tailWord_79472, baseEnd_79472] using wordTrace_append hprefix tailTrace_79472
  have hstable : (prefixWord ++ tailWord_79472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79472).length < 2 ^ (prefixWord ++ tailWord_79472).sum := by decide
  have hdescent : baseEnd_79472 < baseStart_79472 := by decide
  rcases family_descends (prefixWord ++ tailWord_79472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79488 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_79488 : Nat := 118140960795 + 79488 * 2 ^ 59
def prefixEnd_79488 : Nat := 4983230072969 + 3 ^ 40 * 79488 * 2
def baseEnd_79488 : Nat := 13605183421563412178149

theorem tailTrace_79488 : CollatzResearch.WordTrace tailWord_79488 prefixEnd_79488 13605183421563412178149 := by
  unfold tailWord_79488
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449582768018013157355559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1932777024024017543140745 1449582768018013157355559)
  ·
    refine ⟨2174374152027019736033339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449582768018013157355559 2174374152027019736033339)
    ·
      refine ⟨3261561228040529604050009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174374152027019736033339 3261561228040529604050009)
      ·
        refine ⟨2446170921030397203037507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3261561228040529604050009 2446170921030397203037507)
        ·
          refine ⟨3669256381545595804556261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446170921030397203037507 3669256381545595804556261)
          ·
            refine ⟨687985571539799213354299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3669256381545595804556261 687985571539799213354299)
            ·
              refine ⟨1031978357309698820031449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687985571539799213354299 1031978357309698820031449)
              ·
                refine ⟨773983767982274115023587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031978357309698820031449 773983767982274115023587)
                ·
                  refine ⟨1160975651973411172535381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773983767982274115023587 1160975651973411172535381)
                  ·
                    refine ⟨13605183421563412178149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1160975651973411172535381 13605183421563412178149)
                    ·
                      rfl

theorem cell23_79488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_79488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79488 prefixEnd_79488 := by exact prefixLift 79488
  have htrace : WordTrace (prefixWord ++ tailWord_79488) baseStart_79488 baseEnd_79488 := by
    simpa [prefixWord, tailWord_79488, baseEnd_79488] using wordTrace_append hprefix tailTrace_79488
  have hstable : (prefixWord ++ tailWord_79488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79488).length < 2 ^ (prefixWord ++ tailWord_79488).sum := by decide
  have hdescent : baseEnd_79488 < baseStart_79488 := by decide
  rcases family_descends (prefixWord ++ tailWord_79488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79525 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_79525 : Nat := 118140960795 + 79525 * 2 ^ 59
def prefixEnd_79525 : Nat := 4983230072969 + 3 ^ 40 * 79525 * 2
def baseEnd_79525 : Nat := 40834549048906591771777

theorem tailTrace_79525 : CollatzResearch.WordTrace tailWord_79525 prefixEnd_79525 40834549048906591771777 := by
  unfold tailWord_79525
  simp only [CollatzResearch.WordTrace]
  refine ⟨2900515036901981633808029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1933676691267987755872019 2900515036901981633808029)
  ·
    refine ⟨1087693138838243112678011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2900515036901981633808029 1087693138838243112678011)
    ·
      refine ⟨1631539708257364669017017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087693138838243112678011 1631539708257364669017017)
      ·
        refine ⟨1223654781193023501762763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1631539708257364669017017 1223654781193023501762763)
        ·
          refine ⟨1835482171789535252644145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223654781193023501762763 1835482171789535252644145)
          ·
            refine ⟨1376611628842151439483109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835482171789535252644145 1376611628842151439483109)
            ·
              refine ⟨258114680407903394903083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1376611628842151439483109 258114680407903394903083)
              ·
                refine ⟨387172020611855092354625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258114680407903394903083 387172020611855092354625)
                ·
                  refine ⟨290379015458891319265969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387172020611855092354625 290379015458891319265969)
                  ·
                    refine ⟨217784261594168489449477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 290379015458891319265969 217784261594168489449477)
                    ·
                      refine ⟨40834549048906591771777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 217784261594168489449477 40834549048906591771777)
                      ·
                        rfl

theorem cell23_79525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_79525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79525 prefixEnd_79525 := by exact prefixLift 79525
  have htrace : WordTrace (prefixWord ++ tailWord_79525) baseStart_79525 baseEnd_79525 := by
    simpa [prefixWord, tailWord_79525, baseEnd_79525] using wordTrace_append hprefix tailTrace_79525
  have hstable : (prefixWord ++ tailWord_79525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79525).length < 2 ^ (prefixWord ++ tailWord_79525).sum := by decide
  have hdescent : baseEnd_79525 < baseStart_79525 := by decide
  rcases family_descends (prefixWord ++ tailWord_79525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79545 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_79545 : Nat := 118140960795 + 79545 * 2 ^ 59
def prefixEnd_79545 : Nat := 4983230072969 + 3 ^ 40 * 79545 * 2
def baseEnd_79545 : Nat := 40844818661996513521685

theorem tailTrace_79545 : CollatzResearch.WordTrace tailWord_79545 prefixEnd_79545 40844818661996513521685 := by
  unfold tailWord_79545
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901244496829525049536089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1934162997886350033024059 2901244496829525049536089)
  ·
    refine ⟨2175933372622143787152067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2901244496829525049536089 2175933372622143787152067)
    ·
      refine ⟨3263900058933215680728101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2175933372622143787152067 3263900058933215680728101)
      ·
        refine ⟨611981261049977940136519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3263900058933215680728101 611981261049977940136519)
        ·
          refine ⟨917971891574966910204779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611981261049977940136519 917971891574966910204779)
          ·
            refine ⟨1376957837362450365307169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917971891574966910204779 1376957837362450365307169)
            ·
              refine ⟨1032718378021837773980377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376957837362450365307169 1032718378021837773980377)
              ·
                refine ⟨774538783516378330485283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032718378021837773980377 774538783516378330485283)
                ·
                  refine ⟨1161808175274567495727925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774538783516378330485283 1161808175274567495727925)
                  ·
                    refine ⟨108919516431990702724493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1161808175274567495727925 108919516431990702724493)
                    ·
                      refine ⟨40844818661996513521685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 108919516431990702724493 40844818661996513521685)
                      ·
                        rfl

theorem cell23_79545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_79545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79545 prefixEnd_79545 := by exact prefixLift 79545
  have htrace : WordTrace (prefixWord ++ tailWord_79545) baseStart_79545 baseEnd_79545 := by
    simpa [prefixWord, tailWord_79545, baseEnd_79545] using wordTrace_append hprefix tailTrace_79545
  have hstable : (prefixWord ++ tailWord_79545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79545).length < 2 ^ (prefixWord ++ tailWord_79545).sum := by decide
  have hdescent : baseEnd_79545 < baseStart_79545 := by decide
  rcases family_descends (prefixWord ++ tailWord_79545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79569 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 5]
def baseStart_79569 : Nat := 118140960795 + 79569 * 2 ^ 59
def prefixEnd_79569 : Nat := 4983230072969 + 3 ^ 40 * 79569 * 2
def baseEnd_79569 : Nat := 4539682466411602180175

theorem tailTrace_79569 : CollatzResearch.WordTrace tailWord_79569 prefixEnd_79569 4539682466411602180175 := by
  unfold tailWord_79569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902119848742577148409761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1934746565828384765606507 2902119848742577148409761)
  ·
    refine ⟨2176589886556932861307321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2902119848742577148409761 2176589886556932861307321)
    ·
      refine ⟨1632442414917699645980491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2176589886556932861307321 1632442414917699645980491)
      ·
        refine ⟨2448663622376549468970737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632442414917699645980491 2448663622376549468970737)
        ·
          refine ⟨1836497716782412101728053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448663622376549468970737 1836497716782412101728053)
          ·
            refine ⟨172171660948351134537005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1836497716782412101728053 172171660948351134537005)
            ·
              refine ⟨64564372855631675451377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172171660948351134537005 64564372855631675451377)
              ·
                refine ⟨48423279641723756588533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64564372855631675451377 48423279641723756588533)
                ·
                  refine ⟨4539682466411602180175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48423279641723756588533 4539682466411602180175)
                  ·
                    rfl

theorem cell23_79569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 5].length) (baseStart_79569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79569 prefixEnd_79569 := by exact prefixLift 79569
  have htrace : WordTrace (prefixWord ++ tailWord_79569) baseStart_79569 baseEnd_79569 := by
    simpa [prefixWord, tailWord_79569, baseEnd_79569] using wordTrace_append hprefix tailTrace_79569
  have hstable : (prefixWord ++ tailWord_79569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79569).length < 2 ^ (prefixWord ++ tailWord_79569).sum := by decide
  have hdescent : baseEnd_79569 < baseStart_79569 := by decide
  rcases family_descends (prefixWord ++ tailWord_79569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79575 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_79575 : Nat := 118140960795 + 79575 * 2 ^ 59
def prefixEnd_79575 : Nat := 4983230072969 + 3 ^ 40 * 79575 * 2
def baseEnd_79575 : Nat := 40860223081631396146547

theorem tailTrace_79575 : CollatzResearch.WordTrace tailWord_79575 prefixEnd_79575 40860223081631396146547 := by
  unfold tailWord_79575
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902338686720840173128179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1934892457813893448752119 2902338686720840173128179)
  ·
    refine ⟨4353508030081260259692269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2902338686720840173128179 4353508030081260259692269)
    ·
      refine ⟨1632565511280472597384601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4353508030081260259692269 1632565511280472597384601)
      ·
        refine ⟨1224424133460354448038451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1632565511280472597384601 1224424133460354448038451)
        ·
          refine ⟨1836636200190531672057677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224424133460354448038451 1836636200190531672057677)
          ·
            refine ⟨688738575071449377021629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1836636200190531672057677 688738575071449377021629)
            ·
              refine ⟨258276965651793516383111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688738575071449377021629 258276965651793516383111)
              ·
                refine ⟨387415448477690274574667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258276965651793516383111 387415448477690274574667)
                ·
                  refine ⟨581123172716535411862001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387415448477690274574667 581123172716535411862001)
                  ·
                    refine ⟨435842379537401558896501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 581123172716535411862001 435842379537401558896501)
                    ·
                      refine ⟨40860223081631396146547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 435842379537401558896501 40860223081631396146547)
                      ·
                        rfl

theorem cell23_79575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_79575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79575 prefixEnd_79575 := by exact prefixLift 79575
  have htrace : WordTrace (prefixWord ++ tailWord_79575) baseStart_79575 baseEnd_79575 := by
    simpa [prefixWord, tailWord_79575, baseEnd_79575] using wordTrace_append hprefix tailTrace_79575
  have hstable : (prefixWord ++ tailWord_79575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79575).length < 2 ^ (prefixWord ++ tailWord_79575).sum := by decide
  have hdescent : baseEnd_79575 < baseStart_79575 := by decide
  rcases family_descends (prefixWord ++ tailWord_79575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79642 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_79642 : Nat := 118140960795 + 79642 * 2 ^ 59
def prefixEnd_79642 : Nat := 4983230072969 + 3 ^ 40 * 79642 * 2
def baseEnd_79642 : Nat := 4543847365053626000971

theorem tailTrace_79642 : CollatzResearch.WordTrace tailWord_79642 prefixEnd_79642 4543847365053626000971 := by
  unfold tailWord_79642
  simp only [CollatzResearch.WordTrace]
  refine ⟨726195594369527653954295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1936521584985407077211453 726195594369527653954295)
  ·
    refine ⟨1089293391554291480931443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 726195594369527653954295 1089293391554291480931443)
    ·
      refine ⟨1633940087331437221397165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1089293391554291480931443 1633940087331437221397165)
      ·
        refine ⟨612727532749288958023937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1633940087331437221397165 612727532749288958023937)
        ·
          refine ⟨459545649561966718517953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612727532749288958023937 459545649561966718517953)
          ·
            refine ⟨344659237171475038888465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459545649561966718517953 344659237171475038888465)
            ·
              refine ⟨258494427878606279166349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344659237171475038888465 258494427878606279166349)
              ·
                refine ⟨96935410454477354687381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258494427878606279166349 96935410454477354687381)
                ·
                  refine ⟨4543847365053626000971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96935410454477354687381 4543847365053626000971)
                  ·
                    rfl

theorem cell23_79642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_79642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79642 prefixEnd_79642 := by exact prefixLift 79642
  have htrace : WordTrace (prefixWord ++ tailWord_79642) baseStart_79642 baseEnd_79642 := by
    simpa [prefixWord, tailWord_79642, baseEnd_79642] using wordTrace_append hprefix tailTrace_79642
  have hstable : (prefixWord ++ tailWord_79642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79642).length < 2 ^ (prefixWord ++ tailWord_79642).sum := by decide
  have hdescent : baseEnd_79642 < baseStart_79642 := by decide
  rcases family_descends (prefixWord ++ tailWord_79642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79656 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_79656 : Nat := 118140960795 + 79656 * 2 ^ 59
def prefixEnd_79656 : Nat := 4983230072969 + 3 ^ 40 * 79656 * 2
def baseEnd_79656 : Nat := 40901815014645579233675

theorem tailTrace_79656 : CollatzResearch.WordTrace tailWord_79656 prefixEnd_79656 40901815014645579233675 := by
  unfold tailWord_79656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1452646499713695503413411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1936861999618260671217881 1452646499713695503413411)
  ·
    refine ⟨2178969749570543255120117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1452646499713695503413411 2178969749570543255120117)
    ·
      refine ⟨204278414022238430167511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2178969749570543255120117 204278414022238430167511)
      ·
        refine ⟨306417621033357645251267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204278414022238430167511 306417621033357645251267)
        ·
          refine ⟨459626431550036467876901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306417621033357645251267 459626431550036467876901)
          ·
            refine ⟨86179955915631837726919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 459626431550036467876901 86179955915631837726919)
            ·
              refine ⟨129269933873447756590379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86179955915631837726919 129269933873447756590379)
              ·
                refine ⟨193904900810171634885569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129269933873447756590379 193904900810171634885569)
                ·
                  refine ⟨145428675607628726164177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193904900810171634885569 145428675607628726164177)
                  ·
                    refine ⟨109071506705721544623133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145428675607628726164177 109071506705721544623133)
                    ·
                      refine ⟨40901815014645579233675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 109071506705721544623133 40901815014645579233675)
                      ·
                        rfl

theorem cell23_79656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_79656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79656 prefixEnd_79656 := by exact prefixLift 79656
  have htrace : WordTrace (prefixWord ++ tailWord_79656) baseStart_79656 baseEnd_79656 := by
    simpa [prefixWord, tailWord_79656, baseEnd_79656] using wordTrace_append hprefix tailTrace_79656
  have hstable : (prefixWord ++ tailWord_79656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79656).length < 2 ^ (prefixWord ++ tailWord_79656).sum := by decide
  have hdescent : baseEnd_79656 < baseStart_79656 := by decide
  rcases family_descends (prefixWord ++ tailWord_79656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79726 : List Nat := [4, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_79726 : Nat := 118140960795 + 79726 * 2 ^ 59
def prefixEnd_79726 : Nat := 4983230072969 + 3 ^ 40 * 79726 * 2
def baseEnd_79726 : Nat := 40937758660460305358353

theorem tailTrace_79726 : CollatzResearch.WordTrace tailWord_79726 prefixEnd_79726 40937758660460305358353 := by
  unfold tailWord_79726
  simp only [CollatzResearch.WordTrace]
  refine ⟨363480763646724120234379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1938564072782528641250021 363480763646724120234379)
  ·
    refine ⟨545221145470086180351569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363480763646724120234379 545221145470086180351569)
    ·
      refine ⟨408915859102564635263677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 545221145470086180351569 408915859102564635263677)
      ·
        refine ⟨153343447163461738223879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408915859102564635263677 153343447163461738223879)
        ·
          refine ⟨230015170745192607335819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153343447163461738223879 230015170745192607335819)
          ·
            refine ⟨345022756117788911003729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230015170745192607335819 345022756117788911003729)
            ·
              refine ⟨258767067088341683252797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345022756117788911003729 258767067088341683252797)
              ·
                refine ⟨97037650158128131219799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258767067088341683252797 97037650158128131219799)
                ·
                  refine ⟨145556475237192196829699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97037650158128131219799 145556475237192196829699)
                  ·
                    refine ⟨218334712855788295244549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145556475237192196829699 218334712855788295244549)
                    ·
                      refine ⟨40937758660460305358353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 218334712855788295244549 40937758660460305358353)
                      ·
                        rfl

theorem cell23_79726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_79726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79726 prefixEnd_79726 := by exact prefixLift 79726
  have htrace : WordTrace (prefixWord ++ tailWord_79726) baseStart_79726 baseEnd_79726 := by
    simpa [prefixWord, tailWord_79726, baseEnd_79726] using wordTrace_append hprefix tailTrace_79726
  have hstable : (prefixWord ++ tailWord_79726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79726).length < 2 ^ (prefixWord ++ tailWord_79726).sum := by decide
  have hdescent : baseEnd_79726 < baseStart_79726 := by decide
  rcases family_descends (prefixWord ++ tailWord_79726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79729 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_79729 : Nat := 118140960795 + 79729 * 2 ^ 59
def prefixEnd_79729 : Nat := 4983230072969 + 3 ^ 40 * 79729 * 2
def baseEnd_79729 : Nat := 40939299102423793620839

theorem tailTrace_79729 : CollatzResearch.WordTrace tailWord_79729 prefixEnd_79729 40939299102423793620839 := by
  unfold tailWord_79729
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907955528162924474234241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1938637018775282982822827 2907955528162924474234241)
  ·
    refine ⟨2180966646122193355675681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2907955528162924474234241 2180966646122193355675681)
    ·
      refine ⟨1635724984591645016756761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2180966646122193355675681 1635724984591645016756761)
      ·
        refine ⟨1226793738443733762567571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1635724984591645016756761 1226793738443733762567571)
        ·
          refine ⟨1840190607665600643851357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226793738443733762567571 1840190607665600643851357)
          ·
            refine ⟨690071477874600241444259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1840190607665600643851357 690071477874600241444259)
            ·
              refine ⟨1035107216811900362166389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690071477874600241444259 1035107216811900362166389)
              ·
                refine ⟨97041301576115658953099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1035107216811900362166389 97041301576115658953099)
                ·
                  refine ⟨145561952364173488429649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97041301576115658953099 145561952364173488429649)
                  ·
                    refine ⟨109171464273130116322237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145561952364173488429649 109171464273130116322237)
                    ·
                      refine ⟨40939299102423793620839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 109171464273130116322237 40939299102423793620839)
                      ·
                        rfl

theorem cell23_79729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_79729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79729 prefixEnd_79729 := by exact prefixLift 79729
  have htrace : WordTrace (prefixWord ++ tailWord_79729) baseStart_79729 baseEnd_79729 := by
    simpa [prefixWord, tailWord_79729, baseEnd_79729] using wordTrace_append hprefix tailTrace_79729
  have hstable : (prefixWord ++ tailWord_79729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79729).length < 2 ^ (prefixWord ++ tailWord_79729).sum := by decide
  have hdescent : baseEnd_79729 < baseStart_79729 := by decide
  rcases family_descends (prefixWord ++ tailWord_79729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79793 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_79793 : Nat := 118140960795 + 79793 * 2 ^ 59
def prefixEnd_79793 : Nat := 4983230072969 + 3 ^ 40 * 79793 * 2
def baseEnd_79793 : Nat := 40972161864311543220545

theorem tailTrace_79793 : CollatzResearch.WordTrace tailWord_79793 prefixEnd_79793 40972161864311543220545 := by
  unfold tailWord_79793
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910289799931063404564033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1940193199954042269709355 2910289799931063404564033)
  ·
    refine ⟨2182717349948297553423025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2910289799931063404564033 2182717349948297553423025)
    ·
      refine ⟨1637038012461223165067269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2182717349948297553423025 1637038012461223165067269)
      ·
        refine ⟨306944627336479343450113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1637038012461223165067269 306944627336479343450113)
        ·
          refine ⟨230208470502359507587585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306944627336479343450113 230208470502359507587585)
          ·
            refine ⟨172656352876769630690689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230208470502359507587585 172656352876769630690689)
            ·
              refine ⟨129492264657577223018017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172656352876769630690689 129492264657577223018017)
              ·
                refine ⟨97119198493182917263513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129492264657577223018017 97119198493182917263513)
                ·
                  refine ⟨72839398869887187947635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97119198493182917263513 72839398869887187947635)
                  ·
                    refine ⟨109259098304830781921453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72839398869887187947635 109259098304830781921453)
                    ·
                      refine ⟨40972161864311543220545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 109259098304830781921453 40972161864311543220545)
                      ·
                        rfl

theorem cell23_79793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_79793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79793 prefixEnd_79793 := by exact prefixLift 79793
  have htrace : WordTrace (prefixWord ++ tailWord_79793) baseStart_79793 baseEnd_79793 := by
    simpa [prefixWord, tailWord_79793, baseEnd_79793] using wordTrace_append hprefix tailTrace_79793
  have hstable : (prefixWord ++ tailWord_79793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79793).length < 2 ^ (prefixWord ++ tailWord_79793).sum := by decide
  have hdescent : baseEnd_79793 < baseStart_79793 := by decide
  rcases family_descends (prefixWord ++ tailWord_79793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79799 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 5, 4, 2]
def baseStart_79799 : Nat := 118140960795 + 79799 * 2 ^ 59
def prefixEnd_79799 : Nat := 4983230072969 + 3 ^ 40 * 79799 * 2
def baseEnd_79799 : Nat := 40975242748238519745517

theorem tailTrace_79799 : CollatzResearch.WordTrace tailWord_79799 prefixEnd_79799 40975242748238519745517 := by
  unfold tailWord_79799
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910508637909326429282451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1940339091939550952854967 2910508637909326429282451)
  ·
    refine ⟨4365762956863989643923677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910508637909326429282451 4365762956863989643923677)
    ·
      refine ⟨1637161108823996116471379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4365762956863989643923677 1637161108823996116471379)
      ·
        refine ⟨2455741663235994174707069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637161108823996116471379 2455741663235994174707069)
        ·
          refine ⟨920903123713497815515151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2455741663235994174707069 920903123713497815515151)
          ·
            refine ⟨1381354685570246723272727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920903123713497815515151 1381354685570246723272727)
            ·
              refine ⟨2072032028355370084909091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381354685570246723272727 2072032028355370084909091)
              ·
                refine ⟨3108048042533055127363637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072032028355370084909091 3108048042533055127363637)
                ·
                  refine ⟨291379503987473918190341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3108048042533055127363637 291379503987473918190341)
                  ·
                    refine ⟨54633656997651359660689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291379503987473918190341 54633656997651359660689)
                    ·
                      refine ⟨40975242748238519745517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54633656997651359660689 40975242748238519745517)
                      ·
                        rfl

theorem cell23_79799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_79799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79799 prefixEnd_79799 := by exact prefixLift 79799
  have htrace : WordTrace (prefixWord ++ tailWord_79799) baseStart_79799 baseEnd_79799 := by
    simpa [prefixWord, tailWord_79799, baseEnd_79799] using wordTrace_append hprefix tailTrace_79799
  have hstable : (prefixWord ++ tailWord_79799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79799).length < 2 ^ (prefixWord ++ tailWord_79799).sum := by decide
  have hdescent : baseEnd_79799 < baseStart_79799 := by decide
  rcases family_descends (prefixWord ++ tailWord_79799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79802 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_79802 : Nat := 118140960795 + 79802 * 2 ^ 59
def prefixEnd_79802 : Nat := 4983230072969 + 3 ^ 40 * 79802 * 2
def baseEnd_79802 : Nat := 40976783190202008008003

theorem tailTrace_79802 : CollatzResearch.WordTrace tailWord_79802 prefixEnd_79802 40976783190202008008003 := by
  unfold tailWord_79802
  simp only [CollatzResearch.WordTrace]
  refine ⟨727654514224614485410415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1940412037932305294427773 727654514224614485410415)
  ·
    refine ⟨1091481771336921728115623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727654514224614485410415 1091481771336921728115623)
    ·
      refine ⟨1637222657005382592173435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091481771336921728115623 1637222657005382592173435)
      ·
        refine ⟨2455833985508073888260153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637222657005382592173435 2455833985508073888260153)
        ·
          refine ⟨1841875489131055416195115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2455833985508073888260153 1841875489131055416195115)
          ·
            refine ⟨2762813233696583124292673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841875489131055416195115 2762813233696583124292673)
            ·
              refine ⟨2072109925272437343219505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762813233696583124292673 2072109925272437343219505)
              ·
                refine ⟨1554082443954328007414629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072109925272437343219505 1554082443954328007414629)
                ·
                  refine ⟨291390458241436501390243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554082443954328007414629 291390458241436501390243)
                  ·
                    refine ⟨437085687362154752085365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291390458241436501390243 437085687362154752085365)
                    ·
                      refine ⟨40976783190202008008003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 437085687362154752085365 40976783190202008008003)
                      ·
                        rfl

theorem cell23_79802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_79802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79802 prefixEnd_79802 := by exact prefixLift 79802
  have htrace : WordTrace (prefixWord ++ tailWord_79802) baseStart_79802 baseEnd_79802 := by
    simpa [prefixWord, tailWord_79802, baseEnd_79802] using wordTrace_append hprefix tailTrace_79802
  have hstable : (prefixWord ++ tailWord_79802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79802).length < 2 ^ (prefixWord ++ tailWord_79802).sum := by decide
  have hdescent : baseEnd_79802 < baseStart_79802 := by decide
  rcases family_descends (prefixWord ++ tailWord_79802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79816 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_79816 : Nat := 118140960795 + 79816 * 2 ^ 59
def prefixEnd_79816 : Nat := 4983230072969 + 3 ^ 40 * 79816 * 2
def baseEnd_79816 : Nat := 40983971919364953232939

theorem tailTrace_79816 : CollatzResearch.WordTrace tailWord_79816 prefixEnd_79816 40983971919364953232939 := by
  unfold tailWord_79816
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455564339423869166325651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1940752452565158888434201 1455564339423869166325651)
  ·
    refine ⟨2183346509135803749488477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1455564339423869166325651 2183346509135803749488477)
    ·
      refine ⟨818754940925926406058179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2183346509135803749488477 818754940925926406058179)
      ·
        refine ⟨1228132411388889609087269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818754940925926406058179 1228132411388889609087269)
        ·
          refine ⟨230274827135416801703863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1228132411388889609087269 230274827135416801703863)
          ·
            refine ⟨345412240703125202555795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230274827135416801703863 345412240703125202555795)
            ·
              refine ⟨518118361054687803833693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345412240703125202555795 518118361054687803833693)
              ·
                refine ⟨194294385395507926437635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518118361054687803833693 194294385395507926437635)
                ·
                  refine ⟨291441578093261889656453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194294385395507926437635 291441578093261889656453)
                  ·
                    refine ⟨54645295892486604310585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291441578093261889656453 54645295892486604310585)
                    ·
                      refine ⟨40983971919364953232939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54645295892486604310585 40983971919364953232939)
                      ·
                        rfl

theorem cell23_79816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_79816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79816 prefixEnd_79816 := by exact prefixLift 79816
  have htrace : WordTrace (prefixWord ++ tailWord_79816) baseStart_79816 baseEnd_79816 := by
    simpa [prefixWord, tailWord_79816, baseEnd_79816] using wordTrace_append hprefix tailTrace_79816
  have hstable : (prefixWord ++ tailWord_79816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79816).length < 2 ^ (prefixWord ++ tailWord_79816).sum := by decide
  have hdescent : baseEnd_79816 < baseStart_79816 := by decide
  rcases family_descends (prefixWord ++ tailWord_79816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79837 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_79837 : Nat := 118140960795 + 79837 * 2 ^ 59
def prefixEnd_79837 : Nat := 4983230072969 + 3 ^ 40 * 79837 * 2
def baseEnd_79837 : Nat := 40994755013109371070343

theorem tailTrace_79837 : CollatzResearch.WordTrace tailWord_79837 prefixEnd_79837 40994755013109371070343 := by
  unfold tailWord_79837
  simp only [CollatzResearch.WordTrace]
  refine ⟨2911894611771658919165765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1941263074514439279443843 2911894611771658919165765)
  ·
    refine ⟨545980239707186047343581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2911894611771658919165765 545980239707186047343581)
    ·
      refine ⟨204742589890194767753843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 545980239707186047343581 204742589890194767753843)
      ·
        refine ⟨307113884835292151630765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204742589890194767753843 307113884835292151630765)
        ·
          refine ⟨115167706813234556861537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307113884835292151630765 115167706813234556861537)
          ·
            refine ⟨86375780109925917646153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115167706813234556861537 86375780109925917646153)
            ·
              refine ⟨64781835082444438234615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86375780109925917646153 64781835082444438234615)
              ·
                refine ⟨97172752623666657351923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64781835082444438234615 97172752623666657351923)
                ·
                  refine ⟨145759128935499986027885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97172752623666657351923 145759128935499986027885)
                  ·
                    refine ⟨54659673350812494760457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145759128935499986027885 54659673350812494760457)
                    ·
                      refine ⟨40994755013109371070343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54659673350812494760457 40994755013109371070343)
                      ·
                        rfl

theorem cell23_79837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_79837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79837 prefixEnd_79837 := by exact prefixLift 79837
  have htrace : WordTrace (prefixWord ++ tailWord_79837) baseStart_79837 baseEnd_79837 := by
    simpa [prefixWord, tailWord_79837, baseEnd_79837] using wordTrace_append hprefix tailTrace_79837
  have hstable : (prefixWord ++ tailWord_79837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79837).length < 2 ^ (prefixWord ++ tailWord_79837).sum := by decide
  have hdescent : baseEnd_79837 < baseStart_79837 := by decide
  rcases family_descends (prefixWord ++ tailWord_79837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79859 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 7, 2]
def baseStart_79859 : Nat := 118140960795 + 79859 * 2 ^ 59
def prefixEnd_79859 : Nat := 4983230072969 + 3 ^ 40 * 79859 * 2
def baseEnd_79859 : Nat := 41006051587508284995241

theorem tailTrace_79859 : CollatzResearch.WordTrace tailWord_79859 prefixEnd_79859 41006051587508284995241 := by
  unfold tailWord_79859
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912697017691956676466631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1941798011794637784311087 2912697017691956676466631)
  ·
    refine ⟨4369045526537935014699947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2912697017691956676466631 4369045526537935014699947)
    ·
      refine ⟨6553568289806902522049921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369045526537935014699947 6553568289806902522049921)
      ·
        refine ⟨4915176217355176891537441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6553568289806902522049921 4915176217355176891537441)
        ·
          refine ⟨3686382163016382668653081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4915176217355176891537441 3686382163016382668653081)
          ·
            refine ⟨2764786622262287001489811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3686382163016382668653081 2764786622262287001489811)
            ·
              refine ⟨4147179933393430502234717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764786622262287001489811 4147179933393430502234717)
              ·
                refine ⟨1555192475022536438338019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4147179933393430502234717 1555192475022536438338019)
                ·
                  refine ⟨2332788712533804657507029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555192475022536438338019 2332788712533804657507029)
                  ·
                    refine ⟨54674735450011046660321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2332788712533804657507029 54674735450011046660321)
                    ·
                      refine ⟨41006051587508284995241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54674735450011046660321 41006051587508284995241)
                      ·
                        rfl

theorem cell23_79859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7, 2].length) (baseStart_79859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79859 prefixEnd_79859 := by exact prefixLift 79859
  have htrace : WordTrace (prefixWord ++ tailWord_79859) baseStart_79859 baseEnd_79859 := by
    simpa [prefixWord, tailWord_79859, baseEnd_79859] using wordTrace_append hprefix tailTrace_79859
  have hstable : (prefixWord ++ tailWord_79859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79859).length < 2 ^ (prefixWord ++ tailWord_79859).sum := by decide
  have hdescent : baseEnd_79859 < baseStart_79859 := by decide
  rcases family_descends (prefixWord ++ tailWord_79859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79906 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_79906 : Nat := 118140960795 + 79906 * 2 ^ 59
def prefixEnd_79906 : Nat := 4983230072969 + 3 ^ 40 * 79906 * 2
def baseEnd_79906 : Nat := 41030185178269601107525

theorem tailTrace_79906 : CollatzResearch.WordTrace tailWord_79906 prefixEnd_79906 41030185178269601107525 := by
  unfold tailWord_79906
  simp only [CollatzResearch.WordTrace]
  refine ⟨728602812130420925856893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1942940832347789135618381 728602812130420925856893)
  ·
    refine ⟨273226054548907847196335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 728602812130420925856893 273226054548907847196335)
    ·
      refine ⟨409839081823361770794503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273226054548907847196335 409839081823361770794503)
      ·
        refine ⟨614758622735042656191755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409839081823361770794503 614758622735042656191755)
        ·
          refine ⟨922137934102563984287633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614758622735042656191755 922137934102563984287633)
          ·
            refine ⟨691603450576922988215725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922137934102563984287633 691603450576922988215725)
            ·
              refine ⟨259351293966346120580897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691603450576922988215725 259351293966346120580897)
              ·
                refine ⟨194513470474759590435673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259351293966346120580897 194513470474759590435673)
                ·
                  refine ⟨145885102856069692826755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194513470474759590435673 145885102856069692826755)
                  ·
                    refine ⟨218827654284104539240133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145885102856069692826755 218827654284104539240133)
                    ·
                      refine ⟨41030185178269601107525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 218827654284104539240133 41030185178269601107525)
                      ·
                        rfl

theorem cell23_79906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_79906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79906 prefixEnd_79906 := by exact prefixLift 79906
  have htrace : WordTrace (prefixWord ++ tailWord_79906) baseStart_79906 baseEnd_79906 := by
    simpa [prefixWord, tailWord_79906, baseEnd_79906] using wordTrace_append hprefix tailTrace_79906
  have hstable : (prefixWord ++ tailWord_79906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79906).length < 2 ^ (prefixWord ++ tailWord_79906).sum := by decide
  have hdescent : baseEnd_79906 < baseStart_79906 := by decide
  rcases family_descends (prefixWord ++ tailWord_79906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79990 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_79990 : Nat := 118140960795 + 79990 * 2 ^ 59
def prefixEnd_79990 : Nat := 4983230072969 + 3 ^ 40 * 79990 * 2
def baseEnd_79990 : Nat := 41073317553247272457139

theorem tailTrace_79990 : CollatzResearch.WordTrace tailWord_79990 prefixEnd_79990 41073317553247272457139 := by
  unfold tailWord_79990
  simp only [CollatzResearch.WordTrace]
  refine ⟨182342186263585378092839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1944983320144910699656949 182342186263585378092839)
  ·
    refine ⟨273513279395378067139259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182342186263585378092839 273513279395378067139259)
    ·
      refine ⟨410269919093067100708889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273513279395378067139259 410269919093067100708889)
      ·
        refine ⟨307702439319800325531667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410269919093067100708889 307702439319800325531667)
        ·
          refine ⟨461553658979700488297501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307702439319800325531667 461553658979700488297501)
          ·
            refine ⟨173082622117387683111563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461553658979700488297501 173082622117387683111563)
            ·
              refine ⟨259623933176081524667345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173082622117387683111563 259623933176081524667345)
              ·
                refine ⟨194717949882061143500509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259623933176081524667345 194717949882061143500509)
                ·
                  refine ⟨73019231205772928812691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194717949882061143500509 73019231205772928812691)
                  ·
                    refine ⟨109528846808659393219037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73019231205772928812691 109528846808659393219037)
                    ·
                      refine ⟨41073317553247272457139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 109528846808659393219037 41073317553247272457139)
                      ·
                        rfl

theorem cell23_79990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_79990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79990 prefixEnd_79990 := by exact prefixLift 79990
  have htrace : WordTrace (prefixWord ++ tailWord_79990) baseStart_79990 baseEnd_79990 := by
    simpa [prefixWord, tailWord_79990, baseEnd_79990] using wordTrace_append hprefix tailTrace_79990
  have hstable : (prefixWord ++ tailWord_79990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79990).length < 2 ^ (prefixWord ++ tailWord_79990).sum := by decide
  have hdescent : baseEnd_79990 < baseStart_79990 := by decide
  rcases family_descends (prefixWord ++ tailWord_79990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79996 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_79996 : Nat := 118140960795 + 79996 * 2 ^ 59
def prefixEnd_79996 : Nat := 4983230072969 + 3 ^ 40 * 79996 * 2
def baseEnd_79996 : Nat := 41076398437174248982111

theorem tailTrace_79996 : CollatzResearch.WordTrace tailWord_79996 prefixEnd_79996 41076398437174248982111 := by
  unfold tailWord_79996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458846909097814537101921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1945129212130419382802561 1458846909097814537101921)
  ·
    refine ⟨1094135181823360902826441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1458846909097814537101921 1094135181823360902826441)
    ·
      refine ⟨820601386367520677119831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094135181823360902826441 820601386367520677119831)
      ·
        refine ⟨1230902079551281015679747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820601386367520677119831 1230902079551281015679747)
        ·
          refine ⟨1846353119326921523519621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230902079551281015679747 1846353119326921523519621)
          ·
            refine ⟨346191209873797785659929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1846353119326921523519621 346191209873797785659929)
            ·
              refine ⟨259643407405348339244947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346191209873797785659929 259643407405348339244947)
              ·
                refine ⟨389465111108022508867421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259643407405348339244947 389465111108022508867421)
                ·
                  refine ⟨146049416665508440825283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389465111108022508867421 146049416665508440825283)
                  ·
                    refine ⟨219074124998262661237925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146049416665508440825283 219074124998262661237925)
                    ·
                      refine ⟨41076398437174248982111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 219074124998262661237925 41076398437174248982111)
                      ·
                        rfl

theorem cell23_79996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_79996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_79996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_79996 prefixEnd_79996 := by exact prefixLift 79996
  have htrace : WordTrace (prefixWord ++ tailWord_79996) baseStart_79996 baseEnd_79996 := by
    simpa [prefixWord, tailWord_79996, baseEnd_79996] using wordTrace_append hprefix tailTrace_79996
  have hstable : (prefixWord ++ tailWord_79996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79996).length < 2 ^ (prefixWord ++ tailWord_79996).sum := by decide
  have hdescent : baseEnd_79996 < baseStart_79996 := by decide
  rcases family_descends (prefixWord ++ tailWord_79996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80010 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_80010 : Nat := 118140960795 + 80010 * 2 ^ 59
def prefixEnd_80010 : Nat := 4983230072969 + 3 ^ 40 * 80010 * 2
def baseEnd_80010 : Nat := 13694529055445731402349

theorem tailTrace_80010 : CollatzResearch.WordTrace tailWord_80010 prefixEnd_80010 13694529055445731402349 := by
  unfold tailWord_80010
  simp only [CollatzResearch.WordTrace]
  refine ⟨729551110036227366303371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1945469626763272976808989 729551110036227366303371)
  ·
    refine ⟨1094326665054341049455057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 729551110036227366303371 1094326665054341049455057)
    ·
      refine ⟨820744998790755787091293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094326665054341049455057 820744998790755787091293)
      ·
        refine ⟨307779374546533420159235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 820744998790755787091293 307779374546533420159235)
        ·
          refine ⟨461669061819800130238853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307779374546533420159235 461669061819800130238853)
          ·
            refine ⟨86562949091212524419785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 461669061819800130238853 86562949091212524419785)
            ·
              refine ⟨64922211818409393314839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86562949091212524419785 64922211818409393314839)
              ·
                refine ⟨97383317727614089972259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64922211818409393314839 97383317727614089972259)
                ·
                  refine ⟨146074976591421134958389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97383317727614089972259 146074976591421134958389)
                  ·
                    refine ⟨13694529055445731402349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146074976591421134958389 13694529055445731402349)
                    ·
                      rfl

theorem cell23_80010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_80010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80010 prefixEnd_80010 := by exact prefixLift 80010
  have htrace : WordTrace (prefixWord ++ tailWord_80010) baseStart_80010 baseEnd_80010 := by
    simpa [prefixWord, tailWord_80010, baseEnd_80010] using wordTrace_append hprefix tailTrace_80010
  have hstable : (prefixWord ++ tailWord_80010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80010).length < 2 ^ (prefixWord ++ tailWord_80010).sum := by decide
  have hdescent : baseEnd_80010 < baseStart_80010 := by decide
  rcases family_descends (prefixWord ++ tailWord_80010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80023 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 4, 4]
def baseStart_80023 : Nat := 118140960795 + 80023 * 2 ^ 59
def prefixEnd_80023 : Nat := 4983230072969 + 3 ^ 40 * 80023 * 2
def baseEnd_80023 : Nat := 13696754138281881114829

theorem tailTrace_80023 : CollatzResearch.WordTrace tailWord_80023 prefixEnd_80023 13696754138281881114829 := by
  unfold tailWord_80023
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918678589097812685436723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1945785726065208456957815 2918678589097812685436723)
  ·
    refine ⟨4378017883646719028155085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2918678589097812685436723 4378017883646719028155085)
    ·
      refine ⟨1641756706367519635558157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4378017883646719028155085 1641756706367519635558157)
      ·
        refine ⟨615658764887819863334309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1641756706367519635558157 615658764887819863334309)
        ·
          refine ⟨115436018416466224375183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 615658764887819863334309 115436018416466224375183)
          ·
            refine ⟨173154027624699336562775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115436018416466224375183 173154027624699336562775)
            ·
              refine ⟨259731041437049004844163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173154027624699336562775 259731041437049004844163)
              ·
                refine ⟨389596562155573507266245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259731041437049004844163 389596562155573507266245)
                ·
                  refine ⟨73049355404170032612421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 389596562155573507266245 73049355404170032612421)
                  ·
                    refine ⟨13696754138281881114829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73049355404170032612421 13696754138281881114829)
                    ·
                      rfl

theorem cell23_80023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_80023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80023 prefixEnd_80023 := by exact prefixLift 80023
  have htrace : WordTrace (prefixWord ++ tailWord_80023) baseStart_80023 baseEnd_80023 := by
    simpa [prefixWord, tailWord_80023, baseEnd_80023] using wordTrace_append hprefix tailTrace_80023
  have hstable : (prefixWord ++ tailWord_80023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80023).length < 2 ^ (prefixWord ++ tailWord_80023).sum := by decide
  have hdescent : baseEnd_80023 < baseStart_80023 := by decide
  rcases family_descends (prefixWord ++ tailWord_80023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80053 : List Nat := [1, 3, 3, 4, 1, 1, 1, 9]
def baseStart_80053 : Nat := 118140960795 + 80053 * 2 ^ 59
def prefixEnd_80053 : Nat := 4983230072969 + 3 ^ 40 * 80053 * 2
def baseEnd_80053 : Nat := 1522432104980760221087

theorem tailTrace_80053 : CollatzResearch.WordTrace tailWord_80053 prefixEnd_80053 1522432104980760221087 := by
  unfold tailWord_80053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919772778989127809028813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1946515185992751872685875 2919772778989127809028813)
  ·
    refine ⟨1094914792120922928385805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2919772778989127809028813 1094914792120922928385805)
    ·
      refine ⟨410593047045346098144677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1094914792120922928385805 410593047045346098144677)
      ·
        refine ⟨76986196321002393402127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 410593047045346098144677 76986196321002393402127)
        ·
          refine ⟨115479294481503590103191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76986196321002393402127 115479294481503590103191)
          ·
            refine ⟨173218941722255385154787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115479294481503590103191 173218941722255385154787)
            ·
              refine ⟨259828412583383077732181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173218941722255385154787 259828412583383077732181)
              ·
                refine ⟨1522432104980760221087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 259828412583383077732181 1522432104980760221087)
                ·
                  rfl

theorem cell23_80053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 9].length) (baseStart_80053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80053 prefixEnd_80053 := by exact prefixLift 80053
  have htrace : WordTrace (prefixWord ++ tailWord_80053) baseStart_80053 baseEnd_80053 := by
    simpa [prefixWord, tailWord_80053, baseEnd_80053] using wordTrace_append hprefix tailTrace_80053
  have hstable : (prefixWord ++ tailWord_80053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80053).length < 2 ^ (prefixWord ++ tailWord_80053).sum := by decide
  have hdescent : baseEnd_80053 < baseStart_80053 := by decide
  rcases family_descends (prefixWord ++ tailWord_80053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80059 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_80059 : Nat := 118140960795 + 80059 * 2 ^ 59
def prefixEnd_80059 : Nat := 4983230072969 + 3 ^ 40 * 80059 * 2
def baseEnd_80059 : Nat := 41108747718407502494321

theorem tailTrace_80059 : CollatzResearch.WordTrace tailWord_80059 prefixEnd_80059 41108747718407502494321 := by
  unfold tailWord_80059
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919991616967390833747231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1946661077978260555831487 2919991616967390833747231)
  ·
    refine ⟨4379987425451086250620847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2919991616967390833747231 4379987425451086250620847)
    ·
      refine ⟨6569981138176629375931271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379987425451086250620847 6569981138176629375931271)
      ·
        refine ⟨9854971707264944063896907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569981138176629375931271 9854971707264944063896907)
        ·
          refine ⟨14782457560897416095845361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854971707264944063896907 14782457560897416095845361)
          ·
            refine ⟨11086843170673062071884021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14782457560897416095845361 11086843170673062071884021)
            ·
              refine ⟨1039391547250599569239127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11086843170673062071884021 1039391547250599569239127)
              ·
                refine ⟨1559087320875899353858691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039391547250599569239127 1559087320875899353858691)
                ·
                  refine ⟨2338630981313849030788037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1559087320875899353858691 2338630981313849030788037)
                  ·
                    refine ⟨438493308996346693272757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338630981313849030788037 438493308996346693272757)
                    ·
                      refine ⟨41108747718407502494321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 438493308996346693272757 41108747718407502494321)
                      ·
                        rfl

theorem cell23_80059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_80059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80059 prefixEnd_80059 := by exact prefixLift 80059
  have htrace : WordTrace (prefixWord ++ tailWord_80059) baseStart_80059 baseEnd_80059 := by
    simpa [prefixWord, tailWord_80059, baseEnd_80059] using wordTrace_append hprefix tailTrace_80059
  have hstable : (prefixWord ++ tailWord_80059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80059).length < 2 ^ (prefixWord ++ tailWord_80059).sum := by decide
  have hdescent : baseEnd_80059 < baseStart_80059 := by decide
  rcases family_descends (prefixWord ++ tailWord_80059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80064 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 1, 2, 2]
def baseStart_80064 : Nat := 118140960795 + 80064 * 2 ^ 59
def prefixEnd_80064 : Nat := 4983230072969 + 3 ^ 40 * 80064 * 2
def baseEnd_80064 : Nat := 41111315121679982931799

theorem tailTrace_80064 : CollatzResearch.WordTrace tailWord_80064 prefixEnd_80064 41111315121679982931799 := by
  unfold tailWord_80064
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460086990974638343839623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1946782654632851125119497 1460086990974638343839623)
  ·
    refine ⟨2190130486461957515759435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1460086990974638343839623 2190130486461957515759435)
    ·
      refine ⟨3285195729692936273639153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190130486461957515759435 3285195729692936273639153)
      ·
        refine ⟨2463896797269702205229365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3285195729692936273639153 2463896797269702205229365)
        ·
          refine ⟨230990324744034581740253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2463896797269702205229365 230990324744034581740253)
          ·
            refine ⟨86621371779012968152595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230990324744034581740253 86621371779012968152595)
            ·
              refine ⟨129932057668519452228893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86621371779012968152595 129932057668519452228893)
              ·
                refine ⟨48724521625694794585835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129932057668519452228893 48724521625694794585835)
                ·
                  refine ⟨73086782438542191878753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48724521625694794585835 73086782438542191878753)
                  ·
                    refine ⟨54815086828906643909065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73086782438542191878753 54815086828906643909065)
                    ·
                      refine ⟨41111315121679982931799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54815086828906643909065 41111315121679982931799)
                      ·
                        rfl

theorem cell23_80064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_80064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80064 prefixEnd_80064 := by exact prefixLift 80064
  have htrace : WordTrace (prefixWord ++ tailWord_80064) baseStart_80064 baseEnd_80064 := by
    simpa [prefixWord, tailWord_80064, baseEnd_80064] using wordTrace_append hprefix tailTrace_80064
  have hstable : (prefixWord ++ tailWord_80064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80064).length < 2 ^ (prefixWord ++ tailWord_80064).sum := by decide
  have hdescent : baseEnd_80064 < baseStart_80064 := by decide
  rcases family_descends (prefixWord ++ tailWord_80064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80106 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_80106 : Nat := 118140960795 + 80106 * 2 ^ 59
def prefixEnd_80106 : Nat := 4983230072969 + 3 ^ 40 * 80106 * 2
def baseEnd_80106 : Nat := 41132881309168818606605

theorem tailTrace_80106 : CollatzResearch.WordTrace tailWord_80106 prefixEnd_80106 41132881309168818606605 := by
  unfold tailWord_80106
  simp only [CollatzResearch.WordTrace]
  refine ⟨730426461949279465177043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1947803898531411907138781 730426461949279465177043)
  ·
    refine ⟨1095639692923919197765565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730426461949279465177043 1095639692923919197765565)
    ·
      refine ⟨410864884846469699162087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1095639692923919197765565 410864884846469699162087)
      ·
        refine ⟨616297327269704548743131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410864884846469699162087 616297327269704548743131)
        ·
          refine ⟨924445990904556823114697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616297327269704548743131 924445990904556823114697)
          ·
            refine ⟨693334493178417617336023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 924445990904556823114697 693334493178417617336023)
            ·
              refine ⟨1040001739767626426004035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693334493178417617336023 1040001739767626426004035)
              ·
                refine ⟨1560002609651439639006053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040001739767626426004035 1560002609651439639006053)
                ·
                  refine ⟨292500489309644932313635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1560002609651439639006053 292500489309644932313635)
                  ·
                    refine ⟨438750733964467398470453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 292500489309644932313635 438750733964467398470453)
                    ·
                      refine ⟨41132881309168818606605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 438750733964467398470453 41132881309168818606605)
                      ·
                        rfl

theorem cell23_80106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_80106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80106 prefixEnd_80106 := by exact prefixLift 80106
  have htrace : WordTrace (prefixWord ++ tailWord_80106) baseStart_80106 baseEnd_80106 := by
    simpa [prefixWord, tailWord_80106, baseEnd_80106] using wordTrace_append hprefix tailTrace_80106
  have hstable : (prefixWord ++ tailWord_80106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80106).length < 2 ^ (prefixWord ++ tailWord_80106).sum := by decide
  have hdescent : baseEnd_80106 < baseStart_80106 := by decide
  rcases family_descends (prefixWord ++ tailWord_80106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80137 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 2, 2, 2]
def baseStart_80137 : Nat := 118140960795 + 80137 * 2 ^ 59
def prefixEnd_80137 : Nat := 4983230072969 + 3 ^ 40 * 80137 * 2
def baseEnd_80137 : Nat := 41148799209458197318963

theorem tailTrace_80137 : CollatzResearch.WordTrace tailWord_80137 prefixEnd_80137 41148799209458197318963 := by
  unfold tailWord_80137
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922836510684810155086665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948557673789873436724443 2922836510684810155086665)
  ·
    refine ⟨2192127383013607616314999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2922836510684810155086665 2192127383013607616314999)
    ·
      refine ⟨3288191074520411424472499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192127383013607616314999 3288191074520411424472499)
      ·
        refine ⟨4932286611780617136708749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3288191074520411424472499 4932286611780617136708749)
        ·
          refine ⟨1849607479417731426265781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4932286611780617136708749 1849607479417731426265781)
          ·
            refine ⟨173400701195412321212417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1849607479417731426265781 173400701195412321212417)
            ·
              refine ⟨130050525896559240909313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173400701195412321212417 130050525896559240909313)
              ·
                refine ⟨97537894422419430681985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130050525896559240909313 97537894422419430681985)
                ·
                  refine ⟨73153420816814573011489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97537894422419430681985 73153420816814573011489)
                  ·
                    refine ⟨54865065612610929758617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73153420816814573011489 54865065612610929758617)
                    ·
                      refine ⟨41148799209458197318963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54865065612610929758617 41148799209458197318963)
                      ·
                        rfl

theorem cell23_80137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 2, 2].length) (baseStart_80137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80137 prefixEnd_80137 := by exact prefixLift 80137
  have htrace : WordTrace (prefixWord ++ tailWord_80137) baseStart_80137 baseEnd_80137 := by
    simpa [prefixWord, tailWord_80137, baseEnd_80137] using wordTrace_append hprefix tailTrace_80137
  have hstable : (prefixWord ++ tailWord_80137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80137).length < 2 ^ (prefixWord ++ tailWord_80137).sum := by decide
  have hdescent : baseEnd_80137 < baseStart_80137 := by decide
  rcases family_descends (prefixWord ++ tailWord_80137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80156 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_80156 : Nat := 118140960795 + 80156 * 2 ^ 59
def prefixEnd_80156 : Nat := 4983230072969 + 3 ^ 40 * 80156 * 2
def baseEnd_80156 : Nat := 13719518447297874327125

theorem tailTrace_80156 : CollatzResearch.WordTrace tailWord_80156 prefixEnd_80156 13719518447297874327125 := by
  unfold tailWord_80156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461764748807988200014161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1949019665077317600018881 1461764748807988200014161)
  ·
    refine ⟨1096323561605991150010621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1461764748807988200014161 1096323561605991150010621)
    ·
      refine ⟨411121335602246681253983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1096323561605991150010621 411121335602246681253983)
      ·
        refine ⟨616682003403370021880975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411121335602246681253983 616682003403370021880975)
        ·
          refine ⟨925023005105055032821463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616682003403370021880975 925023005105055032821463)
          ·
            refine ⟨1387534507657582549232195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925023005105055032821463 1387534507657582549232195)
            ·
              refine ⟨2081301761486373823848293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387534507657582549232195 2081301761486373823848293)
              ·
                refine ⟨390244080278695091971555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2081301761486373823848293 390244080278695091971555)
                ·
                  refine ⟨585366120418042637957333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390244080278695091971555 585366120418042637957333)
                  ·
                    refine ⟨13719518447297874327125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 585366120418042637957333 13719518447297874327125)
                    ·
                      rfl

theorem cell23_80156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_80156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80156 prefixEnd_80156 := by exact prefixLift 80156
  have htrace : WordTrace (prefixWord ++ tailWord_80156) baseStart_80156 baseEnd_80156 := by
    simpa [prefixWord, tailWord_80156, baseEnd_80156] using wordTrace_append hprefix tailTrace_80156
  have hstable : (prefixWord ++ tailWord_80156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80156).length < 2 ^ (prefixWord ++ tailWord_80156).sum := by decide
  have hdescent : baseEnd_80156 < baseStart_80156 := by decide
  rcases family_descends (prefixWord ++ tailWord_80156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80163 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 2, 5, 2]
def baseStart_80163 : Nat := 118140960795 + 80163 * 2 ^ 59
def prefixEnd_80163 : Nat := 4983230072969 + 3 ^ 40 * 80163 * 2
def baseEnd_80163 : Nat := 41162149706475095593843

theorem tailTrace_80163 : CollatzResearch.WordTrace tailWord_80163 prefixEnd_80163 41162149706475095593843 := by
  unfold tailWord_80163
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923784808590616595533143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1949189872393744397022095 2923784808590616595533143)
  ·
    refine ⟨4385677212885924893299715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923784808590616595533143 4385677212885924893299715)
    ·
      refine ⟨6578515819328887339949573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385677212885924893299715 6578515819328887339949573)
      ·
        refine ⟨1233471716124166376240545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6578515819328887339949573 1233471716124166376240545)
        ·
          refine ⟨925103787093124782180409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1233471716124166376240545 925103787093124782180409)
          ·
            refine ⟨693827840319843586635307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 925103787093124782180409 693827840319843586635307)
            ·
              refine ⟨1040741760479765379952961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693827840319843586635307 1040741760479765379952961)
              ·
                refine ⟨780556320359824034964721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040741760479765379952961 780556320359824034964721)
                ·
                  refine ⟨585417240269868026223541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780556320359824034964721 585417240269868026223541)
                  ·
                    refine ⟨54882866275300127458457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 585417240269868026223541 54882866275300127458457)
                    ·
                      refine ⟨41162149706475095593843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54882866275300127458457 41162149706475095593843)
                      ·
                        rfl

theorem cell23_80163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_80163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80163 prefixEnd_80163 := by exact prefixLift 80163
  have htrace : WordTrace (prefixWord ++ tailWord_80163) baseStart_80163 baseEnd_80163 := by
    simpa [prefixWord, tailWord_80163, baseEnd_80163] using wordTrace_append hprefix tailTrace_80163
  have hstable : (prefixWord ++ tailWord_80163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80163).length < 2 ^ (prefixWord ++ tailWord_80163).sum := by decide
  have hdescent : baseEnd_80163 < baseStart_80163 := by decide
  rcases family_descends (prefixWord ++ tailWord_80163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80210 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_80210 : Nat := 118140960795 + 80210 * 2 ^ 59
def prefixEnd_80210 : Nat := 4983230072969 + 3 ^ 40 * 80210 * 2
def baseEnd_80210 : Nat := 41186283297236411706127

theorem tailTrace_80210 : CollatzResearch.WordTrace tailWord_80210 prefixEnd_80210 41186283297236411706127 := by
  unfold tailWord_80210
  simp only [CollatzResearch.WordTrace]
  refine ⟨731374759855085905623521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1950332692946895748329389 731374759855085905623521)
  ·
    refine ⟨548531069891314429217641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 731374759855085905623521 548531069891314429217641)
    ·
      refine ⟨411398302418485821913231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 548531069891314429217641 411398302418485821913231)
      ·
        refine ⟨617097453627728732869847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411398302418485821913231 617097453627728732869847)
        ·
          refine ⟨925646180441593099304771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617097453627728732869847 925646180441593099304771)
          ·
            refine ⟨1388469270662389648957157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925646180441593099304771 1388469270662389648957157)
            ·
              refine ⟨260337988249198059179467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1388469270662389648957157 260337988249198059179467)
              ·
                refine ⟨390506982373797088769201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260337988249198059179467 390506982373797088769201)
                ·
                  refine ⟨292880236780347816576901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390506982373797088769201 292880236780347816576901)
                  ·
                    refine ⟨54915044396315215608169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 292880236780347816576901 54915044396315215608169)
                    ·
                      refine ⟨41186283297236411706127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54915044396315215608169 41186283297236411706127)
                      ·
                        rfl

theorem cell23_80210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_80210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80210 prefixEnd_80210 := by exact prefixLift 80210
  have htrace : WordTrace (prefixWord ++ tailWord_80210) baseStart_80210 baseEnd_80210 := by
    simpa [prefixWord, tailWord_80210, baseEnd_80210] using wordTrace_append hprefix tailTrace_80210
  have hstable : (prefixWord ++ tailWord_80210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80210).length < 2 ^ (prefixWord ++ tailWord_80210).sum := by decide
  have hdescent : baseEnd_80210 < baseStart_80210 := by decide
  rcases family_descends (prefixWord ++ tailWord_80210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80256 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_80256 : Nat := 118140960795 + 80256 * 2 ^ 59
def prefixEnd_80256 : Nat := 4983230072969 + 3 ^ 40 * 80256 * 2
def baseEnd_80256 : Nat := 41209903407343231730915

theorem tailTrace_80256 : CollatzResearch.WordTrace tailWord_80256 prefixEnd_80256 41209903407343231730915 := by
  unfold tailWord_80256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463588398626846739334311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1951451198169128985779081 1463588398626846739334311)
  ·
    refine ⟨2195382597940270109001467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1463588398626846739334311 2195382597940270109001467)
    ·
      refine ⟨3293073896910405163502201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2195382597940270109001467 3293073896910405163502201)
      ·
        refine ⟨2469805422682803872626651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3293073896910405163502201 2469805422682803872626651)
        ·
          refine ⟨3704708134024205808939977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469805422682803872626651 3704708134024205808939977)
          ·
            refine ⟨2778531100518154356704983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3704708134024205808939977 2778531100518154356704983)
            ·
              refine ⟨4167796650777231535057475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778531100518154356704983 4167796650777231535057475)
              ·
                refine ⟨6251694976165847302586213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167796650777231535057475 6251694976165847302586213)
                ·
                  refine ⟨1172192808031096369234915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6251694976165847302586213 1172192808031096369234915)
                  ·
                    refine ⟨1758289212046644553852373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172192808031096369234915 1758289212046644553852373)
                    ·
                      refine ⟨41209903407343231730915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1758289212046644553852373 41209903407343231730915)
                      ·
                        rfl

theorem cell23_80256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_80256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80256 prefixEnd_80256 := by exact prefixLift 80256
  have htrace : WordTrace (prefixWord ++ tailWord_80256) baseStart_80256 baseEnd_80256 := by
    simpa [prefixWord, tailWord_80256, baseEnd_80256] using wordTrace_append hprefix tailTrace_80256
  have hstable : (prefixWord ++ tailWord_80256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80256).length < 2 ^ (prefixWord ++ tailWord_80256).sum := by decide
  have hdescent : baseEnd_80256 < baseStart_80256 := by decide
  rcases family_descends (prefixWord ++ tailWord_80256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80263 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 3, 5]
def baseStart_80263 : Nat := 118140960795 + 80263 * 2 ^ 59
def prefixEnd_80263 : Nat := 4983230072969 + 3 ^ 40 * 80263 * 2
def baseEnd_80263 : Nat := 13737832590641568114461

theorem tailTrace_80263 : CollatzResearch.WordTrace tailWord_80263 prefixEnd_80263 13737832590641568114461 := by
  unfold tailWord_80263
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927432108228333674173443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1951621405485555782782295 2927432108228333674173443)
  ·
    refine ⟨4391148162342500511260165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2927432108228333674173443 4391148162342500511260165)
    ·
      refine ⟨823340280439218845861281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4391148162342500511260165 823340280439218845861281)
      ·
        refine ⟨617505210329414134395961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 823340280439218845861281 617505210329414134395961)
        ·
          refine ⟨463128907747060600796971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617505210329414134395961 463128907747060600796971)
          ·
            refine ⟨694693361620590901195457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463128907747060600796971 694693361620590901195457)
            ·
              refine ⟨521020021215443175896593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694693361620590901195457 521020021215443175896593)
              ·
                refine ⟨390765015911582381922445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521020021215443175896593 390765015911582381922445)
                ·
                  refine ⟨146536880966843393220917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390765015911582381922445 146536880966843393220917)
                  ·
                    refine ⟨13737832590641568114461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146536880966843393220917 13737832590641568114461)
                    ·
                      rfl

theorem cell23_80263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_80263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80263 prefixEnd_80263 := by exact prefixLift 80263
  have htrace : WordTrace (prefixWord ++ tailWord_80263) baseStart_80263 baseEnd_80263 := by
    simpa [prefixWord, tailWord_80263, baseEnd_80263] using wordTrace_append hprefix tailTrace_80263
  have hstable : (prefixWord ++ tailWord_80263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80263).length < 2 ^ (prefixWord ++ tailWord_80263).sum := by decide
  have hdescent : baseEnd_80263 < baseStart_80263 := by decide
  rcases family_descends (prefixWord ++ tailWord_80263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80280 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_80280 : Nat := 118140960795 + 80280 * 2 ^ 59
def prefixEnd_80280 : Nat := 4983230072969 + 3 ^ 40 * 80280 * 2
def baseEnd_80280 : Nat := 13740742314350379276935

theorem tailTrace_80280 : CollatzResearch.WordTrace tailWord_80280 prefixEnd_80280 13740742314350379276935 := by
  unfold tailWord_80280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464026074583372788771147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1952034766111163718361529 1464026074583372788771147)
  ·
    refine ⟨2196039111875059183156721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1464026074583372788771147 2196039111875059183156721)
    ·
      refine ⟨1647029333906294387367541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2196039111875059183156721 1647029333906294387367541)
      ·
        refine ⟨154409000053715098815707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1647029333906294387367541 154409000053715098815707)
        ·
          refine ⟨231613500080572648223561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154409000053715098815707 231613500080572648223561)
          ·
            refine ⟨173710125060429486167671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231613500080572648223561 173710125060429486167671)
            ·
              refine ⟨260565187590644229251507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173710125060429486167671 260565187590644229251507)
              ·
                refine ⟨390847781385966343877261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260565187590644229251507 390847781385966343877261)
                ·
                  refine ⟨146567918019737378953973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390847781385966343877261 146567918019737378953973)
                  ·
                    refine ⟨13740742314350379276935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146567918019737378953973 13740742314350379276935)
                    ·
                      rfl

theorem cell23_80280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_80280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80280 prefixEnd_80280 := by exact prefixLift 80280
  have htrace : WordTrace (prefixWord ++ tailWord_80280) baseStart_80280 baseEnd_80280 := by
    simpa [prefixWord, tailWord_80280, baseEnd_80280] using wordTrace_append hprefix tailTrace_80280
  have hstable : (prefixWord ++ tailWord_80280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80280).length < 2 ^ (prefixWord ++ tailWord_80280).sum := by decide
  have hdescent : baseEnd_80280 < baseStart_80280 := by decide
  rcases family_descends (prefixWord ++ tailWord_80280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80287 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 2, 3, 2]
def baseStart_80287 : Nat := 118140960795 + 80287 * 2 ^ 59
def prefixEnd_80287 : Nat := 4983230072969 + 3 ^ 40 * 80287 * 2
def baseEnd_80287 : Nat := 41225821307632610443273

theorem tailTrace_80287 : CollatzResearch.WordTrace tailWord_80287 prefixEnd_80287 41225821307632610443273 := by
  unfold tailWord_80287
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928307460141385773047115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1952204973427590515364743 2928307460141385773047115)
  ·
    refine ⟨4392461190212078659570673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928307460141385773047115 4392461190212078659570673)
    ·
      refine ⟨3294345892659058994678005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4392461190212078659570673 3294345892659058994678005)
      ·
        refine ⟨308844927436786780751063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3294345892659058994678005 308844927436786780751063)
        ·
          refine ⟨463267391155180171126595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308844927436786780751063 463267391155180171126595)
          ·
            refine ⟨694901086732770256689893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463267391155180171126595 694901086732770256689893)
            ·
              refine ⟨130293953762394423129355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 694901086732770256689893 130293953762394423129355)
              ·
                refine ⟨195440930643591634694033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130293953762394423129355 195440930643591634694033)
                ·
                  refine ⟨146580697982693726020525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195440930643591634694033 146580697982693726020525)
                  ·
                    refine ⟨54967761743510147257697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146580697982693726020525 54967761743510147257697)
                    ·
                      refine ⟨41225821307632610443273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 54967761743510147257697 41225821307632610443273)
                      ·
                        rfl

theorem cell23_80287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_80287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80287 prefixEnd_80287 := by exact prefixLift 80287
  have htrace : WordTrace (prefixWord ++ tailWord_80287) baseStart_80287 baseEnd_80287 := by
    simpa [prefixWord, tailWord_80287, baseEnd_80287] using wordTrace_append hprefix tailTrace_80287
  have hstable : (prefixWord ++ tailWord_80287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80287).length < 2 ^ (prefixWord ++ tailWord_80287).sum := by decide
  have hdescent : baseEnd_80287 < baseStart_80287 := by decide
  rcases family_descends (prefixWord ++ tailWord_80287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80293 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_80293 : Nat := 118140960795 + 80293 * 2 ^ 59
def prefixEnd_80293 : Nat := 4983230072969 + 3 ^ 40 * 80293 * 2
def baseEnd_80293 : Nat := 13742967397186528989415

theorem tailTrace_80293 : CollatzResearch.WordTrace tailWord_80293 prefixEnd_80293 13742967397186528989415 := by
  unfold tailWord_80293
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928526298119648797765533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1952350865413099198510355 2928526298119648797765533)
  ·
    refine ⟨1098197361794868299162075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2928526298119648797765533 1098197361794868299162075)
    ·
      refine ⟨1647296042692302448743113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1098197361794868299162075 1647296042692302448743113)
      ·
        refine ⟨1235472032019226836557335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1647296042692302448743113 1235472032019226836557335)
        ·
          refine ⟨1853208048028840254836003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235472032019226836557335 1853208048028840254836003)
          ·
            refine ⟨2779812072043260382254005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853208048028840254836003 2779812072043260382254005)
            ·
              refine ⟨260607381754055660836313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2779812072043260382254005 260607381754055660836313)
              ·
                refine ⟨195455536315541745627235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260607381754055660836313 195455536315541745627235)
                ·
                  refine ⟨293183304473312618440853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195455536315541745627235 293183304473312618440853)
                  ·
                    refine ⟨13742967397186528989415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 293183304473312618440853 13742967397186528989415)
                    ·
                      rfl

theorem cell23_80293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_80293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80293 prefixEnd_80293 := by exact prefixLift 80293
  have htrace : WordTrace (prefixWord ++ tailWord_80293) baseStart_80293 baseEnd_80293 := by
    simpa [prefixWord, tailWord_80293, baseEnd_80293] using wordTrace_append hprefix tailTrace_80293
  have hstable : (prefixWord ++ tailWord_80293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80293).length < 2 ^ (prefixWord ++ tailWord_80293).sum := by decide
  have hdescent : baseEnd_80293 < baseStart_80293 := by decide
  rcases family_descends (prefixWord ++ tailWord_80293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80311 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 1, 1, 3]
def baseStart_80311 : Nat := 118140960795 + 80311 * 2 ^ 59
def prefixEnd_80311 : Nat := 4983230072969 + 3 ^ 40 * 80311 * 2
def baseEnd_80311 : Nat := 41238144843340516543163

theorem tailTrace_80311 : CollatzResearch.WordTrace tailWord_80311 prefixEnd_80311 41238144843340516543163 := by
  unfold tailWord_80311
  simp only [CollatzResearch.WordTrace]
  refine ⟨2929182812054437871920787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1952788541369625247947191 2929182812054437871920787)
  ·
    refine ⟨4393774218081656807881181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2929182812054437871920787 4393774218081656807881181)
    ·
      refine ⟨1647665331780621302955443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4393774218081656807881181 1647665331780621302955443)
      ·
        refine ⟨2471497997670931954433165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647665331780621302955443 2471497997670931954433165)
        ·
          refine ⟨926811749126599482912437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2471497997670931954433165 926811749126599482912437)
          ·
            refine ⟨86888601480618701523041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 926811749126599482912437 86888601480618701523041)
            ·
              refine ⟨65166451110464026142281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86888601480618701523041 65166451110464026142281)
              ·
                refine ⟨48874838332848019606711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65166451110464026142281 48874838332848019606711)
                ·
                  refine ⟨73312257499272029410067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48874838332848019606711 73312257499272029410067)
                  ·
                    refine ⟨109968386248908044115101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73312257499272029410067 109968386248908044115101)
                    ·
                      refine ⟨41238144843340516543163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 109968386248908044115101 41238144843340516543163)
                      ·
                        rfl

theorem cell23_80311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_80311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80311 prefixEnd_80311 := by exact prefixLift 80311
  have htrace : WordTrace (prefixWord ++ tailWord_80311) baseStart_80311 baseEnd_80311 := by
    simpa [prefixWord, tailWord_80311, baseEnd_80311] using wordTrace_append hprefix tailTrace_80311
  have hstable : (prefixWord ++ tailWord_80311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80311).length < 2 ^ (prefixWord ++ tailWord_80311).sum := by decide
  have hdescent : baseEnd_80311 < baseStart_80311 := by decide
  rcases family_descends (prefixWord ++ tailWord_80311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80330 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_80330 : Nat := 118140960795 + 80330 * 2 ^ 59
def prefixEnd_80330 : Nat := 4983230072969 + 3 ^ 40 * 80330 * 2
def baseEnd_80330 : Nat := 41247900975775942205575

theorem tailTrace_80330 : CollatzResearch.WordTrace tailWord_80330 prefixEnd_80330 41247900975775942205575 := by
  unfold tailWord_80330
  simp only [CollatzResearch.WordTrace]
  refine ⟨732468949746401029215611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1953250532657069411241629 732468949746401029215611)
  ·
    refine ⟨1098703424619601543823417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 732468949746401029215611 1098703424619601543823417)
    ·
      refine ⟨824027568464701157867563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1098703424619601543823417 824027568464701157867563)
      ·
        refine ⟨1236041352697051736801345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824027568464701157867563 1236041352697051736801345)
        ·
          refine ⟨927031014522788802601009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236041352697051736801345 927031014522788802601009)
          ·
            refine ⟨695273260892091601950757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927031014522788802601009 695273260892091601950757)
            ·
              refine ⟨130363736417267175365767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 695273260892091601950757 130363736417267175365767)
              ·
                refine ⟨195545604625900763048651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130363736417267175365767 195545604625900763048651)
                ·
                  refine ⟨293318406938851144572977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195545604625900763048651 293318406938851144572977)
                  ·
                    refine ⟨219988805204138358429733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293318406938851144572977 219988805204138358429733)
                    ·
                      refine ⟨41247900975775942205575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 219988805204138358429733 41247900975775942205575)
                      ·
                        rfl

theorem cell23_80330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_80330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80330 prefixEnd_80330 := by exact prefixLift 80330
  have htrace : WordTrace (prefixWord ++ tailWord_80330) baseStart_80330 baseEnd_80330 := by
    simpa [prefixWord, tailWord_80330, baseEnd_80330] using wordTrace_append hprefix tailTrace_80330
  have hstable : (prefixWord ++ tailWord_80330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80330).length < 2 ^ (prefixWord ++ tailWord_80330).sum := by decide
  have hdescent : baseEnd_80330 < baseStart_80330 := by decide
  rcases family_descends (prefixWord ++ tailWord_80330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80338 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_80338 : Nat := 118140960795 + 80338 * 2 ^ 59
def prefixEnd_80338 : Nat := 4983230072969 + 3 ^ 40 * 80338 * 2
def baseEnd_80338 : Nat := 41252008821011910905539

theorem tailTrace_80338 : CollatzResearch.WordTrace tailWord_80338 prefixEnd_80338 41252008821011910905539 := by
  unfold tailWord_80338
  simp only [CollatzResearch.WordTrace]
  refine ⟨732541895739155370788417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1953445055304414322102445 732541895739155370788417)
  ·
    refine ⟨549406421804366528091313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 732541895739155370788417 549406421804366528091313)
    ·
      refine ⟨412054816353274896068485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 549406421804366528091313 412054816353274896068485)
      ·
        refine ⟨77260278066239043012841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412054816353274896068485 77260278066239043012841)
        ·
          refine ⟨57945208549679282259631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77260278066239043012841 57945208549679282259631)
          ·
            refine ⟨86917812824518923389447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57945208549679282259631 86917812824518923389447)
            ·
              refine ⟨130376719236778385084171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86917812824518923389447 130376719236778385084171)
              ·
                refine ⟨195565078855167577626257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130376719236778385084171 195565078855167577626257)
                ·
                  refine ⟨146673809141375683219693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195565078855167577626257 146673809141375683219693)
                  ·
                    refine ⟨55002678428015881207385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146673809141375683219693 55002678428015881207385)
                    ·
                      refine ⟨41252008821011910905539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55002678428015881207385 41252008821011910905539)
                      ·
                        rfl

theorem cell23_80338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_80338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80338 prefixEnd_80338 := by exact prefixLift 80338
  have htrace : WordTrace (prefixWord ++ tailWord_80338) baseStart_80338 baseEnd_80338 := by
    simpa [prefixWord, tailWord_80338, baseEnd_80338] using wordTrace_append hprefix tailTrace_80338
  have hstable : (prefixWord ++ tailWord_80338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80338).length < 2 ^ (prefixWord ++ tailWord_80338).sum := by decide
  have hdescent : baseEnd_80338 < baseStart_80338 := by decide
  rcases family_descends (prefixWord ++ tailWord_80338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80351 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 1, 2, 2]
def baseStart_80351 : Nat := 118140960795 + 80351 * 2 ^ 59
def prefixEnd_80351 : Nat := 4983230072969 + 3 ^ 40 * 80351 * 2
def baseEnd_80351 : Nat := 41258684069520360042979

theorem tailTrace_80351 : CollatzResearch.WordTrace tailWord_80351 prefixEnd_80351 41258684069520360042979 := by
  unfold tailWord_80351
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930641731909524703376907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1953761154606349802251271 2930641731909524703376907)
  ·
    refine ⟨4395962597864287055065361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2930641731909524703376907 4395962597864287055065361)
    ·
      refine ⟨3296971948398215291299021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4395962597864287055065361 3296971948398215291299021)
      ·
        refine ⟨1236364480649330734237133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3296971948398215291299021 1236364480649330734237133)
        ·
          refine ⟨463636680243499025338925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1236364480649330734237133 463636680243499025338925)
          ·
            refine ⟨173863755091312134502097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463636680243499025338925 173863755091312134502097)
            ·
              refine ⟨130397816318484100876573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173863755091312134502097 130397816318484100876573)
              ·
                refine ⟨48899181119431537828715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130397816318484100876573 48899181119431537828715)
                ·
                  refine ⟨73348771679147306743073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48899181119431537828715 73348771679147306743073)
                  ·
                    refine ⟨55011578759360480057305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73348771679147306743073 55011578759360480057305)
                    ·
                      refine ⟨41258684069520360042979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55011578759360480057305 41258684069520360042979)
                      ·
                        rfl

theorem cell23_80351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_80351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80351 prefixEnd_80351 := by exact prefixLift 80351
  have htrace : WordTrace (prefixWord ++ tailWord_80351) baseStart_80351 baseEnd_80351 := by
    simpa [prefixWord, tailWord_80351, baseEnd_80351] using wordTrace_append hprefix tailTrace_80351
  have hstable : (prefixWord ++ tailWord_80351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80351).length < 2 ^ (prefixWord ++ tailWord_80351).sum := by decide
  have hdescent : baseEnd_80351 < baseStart_80351 := by decide
  rcases family_descends (prefixWord ++ tailWord_80351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80383 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 2, 6]
def baseStart_80383 : Nat := 118140960795 + 80383 * 2 ^ 59
def prefixEnd_80383 : Nat := 4983230072969 + 3 ^ 40 * 80383 * 2
def baseEnd_80383 : Nat := 13758371816821411614277

theorem tailTrace_80383 : CollatzResearch.WordTrace tailWord_80383 prefixEnd_80383 13758371816821411614277 := by
  unfold tailWord_80383
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931808867793594168541803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1954539245195729445694535 2931808867793594168541803)
  ·
    refine ⟨4397713301690391252812705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931808867793594168541803 4397713301690391252812705)
    ·
      refine ⟨3298284976267793439609529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4397713301690391252812705 3298284976267793439609529)
      ·
        refine ⟨2473713732200845079707147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3298284976267793439609529 2473713732200845079707147)
        ·
          refine ⟨3710570598301267619560721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473713732200845079707147 3710570598301267619560721)
          ·
            refine ⟨2782927948725950714670541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3710570598301267619560721 2782927948725950714670541)
            ·
              refine ⟨1043597980772231518001453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2782927948725950714670541 1043597980772231518001453)
              ·
                refine ⟨391349242789586819250545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043597980772231518001453 391349242789586819250545)
                ·
                  refine ⟨293511932092190114437909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391349242789586819250545 293511932092190114437909)
                  ·
                    refine ⟨13758371816821411614277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 293511932092190114437909 13758371816821411614277)
                    ·
                      rfl

theorem cell23_80383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_80383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80383 prefixEnd_80383 := by exact prefixLift 80383
  have htrace : WordTrace (prefixWord ++ tailWord_80383) baseStart_80383 baseEnd_80383 := by
    simpa [prefixWord, tailWord_80383, baseEnd_80383] using wordTrace_append hprefix tailTrace_80383
  have hstable : (prefixWord ++ tailWord_80383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80383).length < 2 ^ (prefixWord ++ tailWord_80383).sum := by decide
  have hdescent : baseEnd_80383 < baseStart_80383 := by decide
  rcases family_descends (prefixWord ++ tailWord_80383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80394 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_80394 : Nat := 118140960795 + 80394 * 2 ^ 59
def prefixEnd_80394 : Nat := 4983230072969 + 3 ^ 40 * 80394 * 2
def baseEnd_80394 : Nat := 41280763737663691805281

theorem tailTrace_80394 : CollatzResearch.WordTrace tailWord_80394 prefixEnd_80394 41280763737663691805281 := by
  unfold tailWord_80394
  simp only [CollatzResearch.WordTrace]
  refine ⟨733052517688435761798059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1954806713835828698128157 733052517688435761798059)
  ·
    refine ⟨1099578776532653642697089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733052517688435761798059 1099578776532653642697089)
    ·
      refine ⟨824684082399490232022817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1099578776532653642697089 824684082399490232022817)
      ·
        refine ⟨618513061799617674017113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824684082399490232022817 618513061799617674017113)
        ·
          refine ⟨463884796349713255512835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618513061799617674017113 463884796349713255512835)
          ·
            refine ⟨695827194524569883269253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463884796349713255512835 695827194524569883269253)
            ·
              refine ⟨130467598973356853112985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 695827194524569883269253 130467598973356853112985)
              ·
                refine ⟨97850699230017639834739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130467598973356853112985 97850699230017639834739)
                ·
                  refine ⟨146776048845026459752109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97850699230017639834739 146776048845026459752109)
                  ·
                    refine ⟨55041018316884922407041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146776048845026459752109 55041018316884922407041)
                    ·
                      refine ⟨41280763737663691805281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55041018316884922407041 41280763737663691805281)
                      ·
                        rfl

theorem cell23_80394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_80394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80394 prefixEnd_80394 := by exact prefixLift 80394
  have htrace : WordTrace (prefixWord ++ tailWord_80394) baseStart_80394 baseEnd_80394 := by
    simpa [prefixWord, tailWord_80394, baseEnd_80394] using wordTrace_append hprefix tailTrace_80394
  have hstable : (prefixWord ++ tailWord_80394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80394).length < 2 ^ (prefixWord ++ tailWord_80394).sum := by decide
  have hdescent : baseEnd_80394 < baseStart_80394 := by decide
  rcases family_descends (prefixWord ++ tailWord_80394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80440 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_80440 : Nat := 118140960795 + 80440 * 2 ^ 59
def prefixEnd_80440 : Nat := 4983230072969 + 3 ^ 40 * 80440 * 2
def baseEnd_80440 : Nat := 41304383847770511830069

theorem tailTrace_80440 : CollatzResearch.WordTrace tailWord_80440 prefixEnd_80440 41304383847770511830069 := by
  unfold tailWord_80440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466943914293546451683387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1955925219058061935577849 1466943914293546451683387)
  ·
    refine ⟨2200415871440319677525081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466943914293546451683387 2200415871440319677525081)
    ·
      refine ⟨1650311903580239758143811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2200415871440319677525081 1650311903580239758143811)
      ·
        refine ⟨2475467855370359637215717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650311903580239758143811 2475467855370359637215717)
        ·
          refine ⟨464150222881942431977947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2475467855370359637215717 464150222881942431977947)
          ·
            refine ⟨696225334322913647966921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464150222881942431977947 696225334322913647966921)
            ·
              refine ⟨522169000742185235975191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696225334322913647966921 522169000742185235975191)
              ·
                refine ⟨783253501113277853962787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522169000742185235975191 783253501113277853962787)
                ·
                  refine ⟨1174880251669916780944181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783253501113277853962787 1174880251669916780944181)
                  ·
                    refine ⟨110145023594054698213517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1174880251669916780944181 110145023594054698213517)
                    ·
                      refine ⟨41304383847770511830069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110145023594054698213517 41304383847770511830069)
                      ·
                        rfl

theorem cell23_80440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_80440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80440 prefixEnd_80440 := by exact prefixLift 80440
  have htrace : WordTrace (prefixWord ++ tailWord_80440) baseStart_80440 baseEnd_80440 := by
    simpa [prefixWord, tailWord_80440, baseEnd_80440] using wordTrace_append hprefix tailTrace_80440
  have hstable : (prefixWord ++ tailWord_80440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80440).length < 2 ^ (prefixWord ++ tailWord_80440).sum := by decide
  have hdescent : baseEnd_80440 < baseStart_80440 := by decide
  rcases family_descends (prefixWord ++ tailWord_80440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80517 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_80517 : Nat := 118140960795 + 80517 * 2 ^ 59
def prefixEnd_80517 : Nat := 4983230072969 + 3 ^ 40 * 80517 * 2
def baseEnd_80517 : Nat := 41343921858166710567215

theorem tailTrace_80517 : CollatzResearch.WordTrace tailWord_80517 prefixEnd_80517 41343921858166710567215 := by
  unfold tailWord_80517
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936696249308135053919805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1957797499538756702613203 2936696249308135053919805)
  ·
    refine ⟨1101261093490550645219927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2936696249308135053919805 1101261093490550645219927)
    ·
      refine ⟨1651891640235825967829891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101261093490550645219927 1651891640235825967829891)
      ·
        refine ⟨2477837460353738951744837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651891640235825967829891 2477837460353738951744837)
        ·
          refine ⟨464594523816326053452157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2477837460353738951744837 464594523816326053452157)
          ·
            refine ⟨174222946431122270044559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464594523816326053452157 174222946431122270044559)
            ·
              refine ⟨261334419646683405066839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174222946431122270044559 261334419646683405066839)
              ·
                refine ⟨392001629470025107600259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261334419646683405066839 392001629470025107600259)
                ·
                  refine ⟨588002444205037661400389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392001629470025107600259 588002444205037661400389)
                  ·
                    refine ⟨110250458288444561512573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 588002444205037661400389 110250458288444561512573)
                    ·
                      refine ⟨41343921858166710567215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110250458288444561512573 41343921858166710567215)
                      ·
                        rfl

theorem cell23_80517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_80517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80517 prefixEnd_80517 := by exact prefixLift 80517
  have htrace : WordTrace (prefixWord ++ tailWord_80517) baseStart_80517 baseEnd_80517 := by
    simpa [prefixWord, tailWord_80517, baseEnd_80517] using wordTrace_append hprefix tailTrace_80517
  have hstable : (prefixWord ++ tailWord_80517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80517).length < 2 ^ (prefixWord ++ tailWord_80517).sum := by decide
  have hdescent : baseEnd_80517 < baseStart_80517 := by decide
  rcases family_descends (prefixWord ++ tailWord_80517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80574 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_80574 : Nat := 118140960795 + 80574 * 2 ^ 59
def prefixEnd_80574 : Nat := 4983230072969 + 3 ^ 40 * 80574 * 2
def baseEnd_80574 : Nat := 41373190255472987554453

theorem tailTrace_80574 : CollatzResearch.WordTrace tailWord_80574 prefixEnd_80574 41373190255472987554453 := by
  unfold tailWord_80574
  simp only [CollatzResearch.WordTrace]
  refine ⟨367346901262704223593097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1959183473401089192496517 367346901262704223593097)
  ·
    refine ⟨275510175947028167694823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 367346901262704223593097 275510175947028167694823)
    ·
      refine ⟨413265263920542251542235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275510175947028167694823 413265263920542251542235)
      ·
        refine ⟨619897895880813377313353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413265263920542251542235 619897895880813377313353)
        ·
          refine ⟨464923421910610032985015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619897895880813377313353 464923421910610032985015)
          ·
            refine ⟨697385132865915049477523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464923421910610032985015 697385132865915049477523)
            ·
              refine ⟨1046077699298872574216285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697385132865915049477523 1046077699298872574216285)
              ·
                refine ⟨392279137237077215331107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1046077699298872574216285 392279137237077215331107)
                ·
                  refine ⟨588418705855615822996661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392279137237077215331107 588418705855615822996661)
                  ·
                    refine ⟨55164253673963983405937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 588418705855615822996661 55164253673963983405937)
                    ·
                      refine ⟨41373190255472987554453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55164253673963983405937 41373190255472987554453)
                      ·
                        rfl

theorem cell23_80574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_80574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80574 prefixEnd_80574 := by exact prefixLift 80574
  have htrace : WordTrace (prefixWord ++ tailWord_80574) baseStart_80574 baseEnd_80574 := by
    simpa [prefixWord, tailWord_80574, baseEnd_80574] using wordTrace_append hprefix tailTrace_80574
  have hstable : (prefixWord ++ tailWord_80574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80574).length < 2 ^ (prefixWord ++ tailWord_80574).sum := by decide
  have hdescent : baseEnd_80574 < baseStart_80574 := by decide
  rcases family_descends (prefixWord ++ tailWord_80574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80607 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_80607 : Nat := 118140960795 + 80607 * 2 ^ 59
def prefixEnd_80607 : Nat := 4983230072969 + 3 ^ 40 * 80607 * 2
def baseEnd_80607 : Nat := 41390135117071358441801

theorem tailTrace_80607 : CollatzResearch.WordTrace tailWord_80607 prefixEnd_80607 41390135117071358441801 := by
  unfold tailWord_80607
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939978818982080424696075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1959985879321386949797383 2939978818982080424696075)
  ·
    refine ⟨4409968228473120637044113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939978818982080424696075 4409968228473120637044113)
    ·
      refine ⟨3307476171354840477783085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409968228473120637044113 3307476171354840477783085)
      ·
        refine ⟨1240303564258065179168657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3307476171354840477783085 1240303564258065179168657)
        ·
          refine ⟨930227673193548884376493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240303564258065179168657 930227673193548884376493)
          ·
            refine ⟨348835377447580831641185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 930227673193548884376493 348835377447580831641185)
            ·
              refine ⟨261626533085685623730889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348835377447580831641185 261626533085685623730889)
              ·
                refine ⟨196219899814264217798167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261626533085685623730889 196219899814264217798167)
                ·
                  refine ⟨294329849721396326697251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196219899814264217798167 294329849721396326697251)
                  ·
                    refine ⟨441494774582094490045877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294329849721396326697251 441494774582094490045877)
                    ·
                      refine ⟨41390135117071358441801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 441494774582094490045877 41390135117071358441801)
                      ·
                        rfl

theorem cell23_80607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_80607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80607 prefixEnd_80607 := by exact prefixLift 80607
  have htrace : WordTrace (prefixWord ++ tailWord_80607) baseStart_80607 baseEnd_80607 := by
    simpa [prefixWord, tailWord_80607, baseEnd_80607] using wordTrace_append hprefix tailTrace_80607
  have hstable : (prefixWord ++ tailWord_80607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80607).length < 2 ^ (prefixWord ++ tailWord_80607).sum := by decide
  have hdescent : baseEnd_80607 < baseStart_80607 := by decide
  rcases family_descends (prefixWord ++ tailWord_80607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80621 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_80621 : Nat := 118140960795 + 80621 * 2 ^ 59
def prefixEnd_80621 : Nat := 4983230072969 + 3 ^ 40 * 80621 * 2
def baseEnd_80621 : Nat := 41397323846234303666737

theorem tailTrace_80621 : CollatzResearch.WordTrace tailWord_80621 prefixEnd_80621 41397323846234303666737 := by
  unfold tailWord_80621
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940489440931360815705717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1960326293954240543803811 2940489440931360815705717)
  ·
    refine ⟨275670885087315076472411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2940489440931360815705717 275670885087315076472411)
    ·
      refine ⟨413506327630972614708617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275670885087315076472411 413506327630972614708617)
      ·
        refine ⟨310129745723229461031463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 413506327630972614708617 310129745723229461031463)
        ·
          refine ⟨465194618584844191547195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310129745723229461031463 465194618584844191547195)
          ·
            refine ⟨697791927877266287320793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465194618584844191547195 697791927877266287320793)
            ·
              refine ⟨523343945907949715490595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697791927877266287320793 523343945907949715490595)
              ·
                refine ⟨785015918861924573235893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523343945907949715490595 785015918861924573235893)
                ·
                  refine ⟨73595242393305428740865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 785015918861924573235893 73595242393305428740865)
                  ·
                    refine ⟨55196431794979071555649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73595242393305428740865 55196431794979071555649)
                    ·
                      refine ⟨41397323846234303666737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55196431794979071555649 41397323846234303666737)
                      ·
                        rfl

theorem cell23_80621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_80621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80621 prefixEnd_80621 := by exact prefixLift 80621
  have htrace : WordTrace (prefixWord ++ tailWord_80621) baseStart_80621 baseEnd_80621 := by
    simpa [prefixWord, tailWord_80621, baseEnd_80621] using wordTrace_append hprefix tailTrace_80621
  have hstable : (prefixWord ++ tailWord_80621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80621).length < 2 ^ (prefixWord ++ tailWord_80621).sum := by decide
  have hdescent : baseEnd_80621 < baseStart_80621 := by decide
  rcases family_descends (prefixWord ++ tailWord_80621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80638 : List Nat := [4, 2, 2, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_80638 : Nat := 118140960795 + 80638 * 2 ^ 59
def prefixEnd_80638 : Nat := 4983230072969 + 3 ^ 40 * 80638 * 2
def baseEnd_80638 : Nat := 41406053017360737154159

theorem tailTrace_80638 : CollatzResearch.WordTrace tailWord_80638 prefixEnd_80638 41406053017360737154159 := by
  unfold tailWord_80638
  simp only [CollatzResearch.WordTrace]
  refine ⟨367638685233721589884321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1960739654579848479383045 367638685233721589884321)
  ·
    refine ⟨275729013925291192413241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 367638685233721589884321 275729013925291192413241)
    ·
      refine ⟨206796760443968394309931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275729013925291192413241 206796760443968394309931)
      ·
        refine ⟨310195140665952591464897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206796760443968394309931 310195140665952591464897)
        ·
          refine ⟨232646355499464443598673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310195140665952591464897 232646355499464443598673)
          ·
            refine ⟨174484766624598332699005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232646355499464443598673 174484766624598332699005)
            ·
              refine ⟨65431787484224374762127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174484766624598332699005 65431787484224374762127)
              ·
                refine ⟨98147681226336562143191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65431787484224374762127 98147681226336562143191)
                ·
                  refine ⟨147221521839504843214787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98147681226336562143191 147221521839504843214787)
                  ·
                    refine ⟨220832282759257264822181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147221521839504843214787 220832282759257264822181)
                    ·
                      refine ⟨41406053017360737154159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 220832282759257264822181 41406053017360737154159)
                      ·
                        rfl

theorem cell23_80638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_80638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80638 prefixEnd_80638 := by exact prefixLift 80638
  have htrace : WordTrace (prefixWord ++ tailWord_80638) baseStart_80638 baseEnd_80638 := by
    simpa [prefixWord, tailWord_80638, baseEnd_80638] using wordTrace_append hprefix tailTrace_80638
  have hstable : (prefixWord ++ tailWord_80638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80638).length < 2 ^ (prefixWord ++ tailWord_80638).sum := by decide
  have hdescent : baseEnd_80638 < baseStart_80638 := by decide
  rcases family_descends (prefixWord ++ tailWord_80638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80640 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_80640 : Nat := 118140960795 + 80640 * 2 ^ 59
def prefixEnd_80640 : Nat := 4983230072969 + 3 ^ 40 * 80640 * 2
def baseEnd_80640 : Nat := 13802359992889909776383

theorem tailTrace_80640 : CollatzResearch.WordTrace tailWord_80640 prefixEnd_80640 13802359992889909776383 := by
  unfold tailWord_80640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470591213931263530323687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1960788285241684707098249 1470591213931263530323687)
  ·
    refine ⟨2205886820896895295485531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470591213931263530323687 2205886820896895295485531)
    ·
      refine ⟨3308830231345342943228297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205886820896895295485531 3308830231345342943228297)
      ·
        refine ⟨2481622673509007207421223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3308830231345342943228297 2481622673509007207421223)
        ·
          refine ⟨3722434010263510811131835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481622673509007207421223 3722434010263510811131835)
          ·
            refine ⟨5583651015395266216697753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722434010263510811131835 5583651015395266216697753)
            ·
              refine ⟨4187738261546449662523315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5583651015395266216697753 4187738261546449662523315)
              ·
                refine ⟨6281607392319674493784973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4187738261546449662523315 6281607392319674493784973)
                ·
                  refine ⟨2355602772119877935169365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6281607392319674493784973 2355602772119877935169365)
                  ·
                    refine ⟨13802359992889909776383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2355602772119877935169365 13802359992889909776383)
                    ·
                      rfl

theorem cell23_80640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_80640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80640 prefixEnd_80640 := by exact prefixLift 80640
  have htrace : WordTrace (prefixWord ++ tailWord_80640) baseStart_80640 baseEnd_80640 := by
    simpa [prefixWord, tailWord_80640, baseEnd_80640] using wordTrace_append hprefix tailTrace_80640
  have hstable : (prefixWord ++ tailWord_80640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80640).length < 2 ^ (prefixWord ++ tailWord_80640).sum := by decide
  have hdescent : baseEnd_80640 < baseStart_80640 := by decide
  rcases family_descends (prefixWord ++ tailWord_80640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80671 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 3]
def baseStart_80671 : Nat := 118140960795 + 80671 * 2 ^ 59
def prefixEnd_80671 : Nat := 4983230072969 + 3 ^ 40 * 80671 * 2
def baseEnd_80671 : Nat := 41422997878959108041507

theorem tailTrace_80671 : CollatzResearch.WordTrace tailWord_80671 prefixEnd_80671 41422997878959108041507 := by
  unfold tailWord_80671
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942313090750219355025867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1961542060500146236683911 2942313090750219355025867)
  ·
    refine ⟨4413469636125329032538801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2942313090750219355025867 4413469636125329032538801)
    ·
      refine ⟨3310102227093996774404101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4413469636125329032538801 3310102227093996774404101)
      ·
        refine ⟨620644167580124395200769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3310102227093996774404101 620644167580124395200769)
        ·
          refine ⟨465483125685093296400577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620644167580124395200769 465483125685093296400577)
          ·
            refine ⟨349112344263819972300433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465483125685093296400577 349112344263819972300433)
            ·
              refine ⟨261834258197864979225325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349112344263819972300433 261834258197864979225325)
              ·
                refine ⟨98187846824199367209497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261834258197864979225325 98187846824199367209497)
                ·
                  refine ⟨73640885118149525407123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98187846824199367209497 73640885118149525407123)
                  ·
                    refine ⟨110461327677224288110685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73640885118149525407123 110461327677224288110685)
                    ·
                      refine ⟨41422997878959108041507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110461327677224288110685 41422997878959108041507)
                      ·
                        rfl

theorem cell23_80671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_80671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80671 prefixEnd_80671 := by exact prefixLift 80671
  have htrace : WordTrace (prefixWord ++ tailWord_80671) baseStart_80671 baseEnd_80671 := by
    simpa [prefixWord, tailWord_80671, baseEnd_80671] using wordTrace_append hprefix tailTrace_80671
  have hstable : (prefixWord ++ tailWord_80671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80671).length < 2 ^ (prefixWord ++ tailWord_80671).sum := by decide
  have hdescent : baseEnd_80671 < baseStart_80671 := by decide
  rcases family_descends (prefixWord ++ tailWord_80671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80677 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_80677 : Nat := 118140960795 + 80677 * 2 ^ 59
def prefixEnd_80677 : Nat := 4983230072969 + 3 ^ 40 * 80677 * 2
def baseEnd_80677 : Nat := 41426078762886084566479

theorem tailTrace_80677 : CollatzResearch.WordTrace tailWord_80677 prefixEnd_80677 41426078762886084566479 := by
  unfold tailWord_80677
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942531928728482379744285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1961687952485654919829523 2942531928728482379744285)
  ·
    refine ⟨1103449473273180892404107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2942531928728482379744285 1103449473273180892404107)
    ·
      refine ⟨1655174209909771338606161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103449473273180892404107 1655174209909771338606161)
      ·
        refine ⟨1241380657432328503954621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1655174209909771338606161 1241380657432328503954621)
        ·
          refine ⟨465517746537123188982983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1241380657432328503954621 465517746537123188982983)
          ·
            refine ⟨698276619805684783474475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465517746537123188982983 698276619805684783474475)
            ·
              refine ⟨1047414929708527175211713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698276619805684783474475 1047414929708527175211713)
              ·
                refine ⟨785561197281395381408785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047414929708527175211713 785561197281395381408785)
                ·
                  refine ⟨589170897961046536056589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 785561197281395381408785 589170897961046536056589)
                  ·
                    refine ⟨220939086735392451021221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 589170897961046536056589 220939086735392451021221)
                    ·
                      refine ⟨41426078762886084566479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 220939086735392451021221 41426078762886084566479)
                      ·
                        rfl

theorem cell23_80677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_80677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80677 prefixEnd_80677 := by exact prefixLift 80677
  have htrace : WordTrace (prefixWord ++ tailWord_80677) baseStart_80677 baseEnd_80677 := by
    simpa [prefixWord, tailWord_80677, baseEnd_80677] using wordTrace_append hprefix tailTrace_80677
  have hstable : (prefixWord ++ tailWord_80677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80677).length < 2 ^ (prefixWord ++ tailWord_80677).sum := by decide
  have hdescent : baseEnd_80677 < baseStart_80677 := by decide
  rcases family_descends (prefixWord ++ tailWord_80677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80692 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_80692 : Nat := 118140960795 + 80692 * 2 ^ 59
def prefixEnd_80692 : Nat := 4983230072969 + 3 ^ 40 * 80692 * 2
def baseEnd_80692 : Nat := 41433780972703525878911

theorem tailTrace_80692 : CollatzResearch.WordTrace tailWord_80692 prefixEnd_80692 41433780972703525878911 := by
  unfold tailWord_80692
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471539511837069970770165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1962052682449426627693553 1471539511837069970770165)
  ·
    refine ⟨137956829234725309759703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1471539511837069970770165 137956829234725309759703)
    ·
      refine ⟨206935243852087964639555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137956829234725309759703 206935243852087964639555)
      ·
        refine ⟨310402865778131946959333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206935243852087964639555 310402865778131946959333)
        ·
          refine ⟨58200537333399740054875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310402865778131946959333 58200537333399740054875)
          ·
            refine ⟨87300806000099610082313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58200537333399740054875 87300806000099610082313)
            ·
              refine ⟨65475604500074707561735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87300806000099610082313 65475604500074707561735)
              ·
                refine ⟨98213406750112061342603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65475604500074707561735 98213406750112061342603)
                ·
                  refine ⟨147320110125168092013905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98213406750112061342603 147320110125168092013905)
                  ·
                    refine ⟨110490082593876069010429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147320110125168092013905 110490082593876069010429)
                    ·
                      refine ⟨41433780972703525878911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110490082593876069010429 41433780972703525878911)
                      ·
                        rfl

theorem cell23_80692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_80692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80692 prefixEnd_80692 := by exact prefixLift 80692
  have htrace : WordTrace (prefixWord ++ tailWord_80692) baseStart_80692 baseEnd_80692 := by
    simpa [prefixWord, tailWord_80692, baseEnd_80692] using wordTrace_append hprefix tailTrace_80692
  have hstable : (prefixWord ++ tailWord_80692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80692).length < 2 ^ (prefixWord ++ tailWord_80692).sum := by decide
  have hdescent : baseEnd_80692 < baseStart_80692 := by decide
  rcases family_descends (prefixWord ++ tailWord_80692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80698 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2]
def baseStart_80698 : Nat := 118140960795 + 80698 * 2 ^ 59
def prefixEnd_80698 : Nat := 4983230072969 + 3 ^ 40 * 80698 * 2
def baseEnd_80698 : Nat := 41436861856630502403883

theorem tailTrace_80698 : CollatzResearch.WordTrace tailWord_80698 prefixEnd_80698 41436861856630502403883 := by
  unfold tailWord_80698
  simp only [CollatzResearch.WordTrace]
  refine ⟨735824465413100741564687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1962198574434935310839165 735824465413100741564687)
  ·
    refine ⟨1103736698119651112347031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 735824465413100741564687 1103736698119651112347031)
    ·
      refine ⟨1655605047179476668520547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103736698119651112347031 1655605047179476668520547)
      ·
        refine ⟨2483407570769215002780821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655605047179476668520547 2483407570769215002780821)
        ·
          refine ⟨116409729879806953255351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2483407570769215002780821 116409729879806953255351)
          ·
            refine ⟨174614594819710429883027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116409729879806953255351 174614594819710429883027)
            ·
              refine ⟨261921892229565644824541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174614594819710429883027 261921892229565644824541)
              ·
                refine ⟨98220709586087116809203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261921892229565644824541 98220709586087116809203)
                ·
                  refine ⟨147331064379130675213805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98220709586087116809203 147331064379130675213805)
                  ·
                    refine ⟨55249149142174003205177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147331064379130675213805 55249149142174003205177)
                    ·
                      refine ⟨41436861856630502403883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55249149142174003205177 41436861856630502403883)
                      ·
                        rfl

theorem cell23_80698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_80698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80698 prefixEnd_80698 := by exact prefixLift 80698
  have htrace : WordTrace (prefixWord ++ tailWord_80698) baseStart_80698 baseEnd_80698 := by
    simpa [prefixWord, tailWord_80698, baseEnd_80698] using wordTrace_append hprefix tailTrace_80698
  have hstable : (prefixWord ++ tailWord_80698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80698).length < 2 ^ (prefixWord ++ tailWord_80698).sum := by decide
  have hdescent : baseEnd_80698 < baseStart_80698 := by decide
  rcases family_descends (prefixWord ++ tailWord_80698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80707 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4]
def baseStart_80707 : Nat := 118140960795 + 80707 * 2 ^ 59
def prefixEnd_80707 : Nat := 4983230072969 + 3 ^ 40 * 80707 * 2
def baseEnd_80707 : Nat := 41441483182520967191341

theorem tailTrace_80707 : CollatzResearch.WordTrace tailWord_80707 prefixEnd_80707 41441483182520967191341 := by
  unfold tailWord_80707
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943626118619797503336375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1962417412413198335557583 2943626118619797503336375)
  ·
    refine ⟨4415439177929696255004563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2943626118619797503336375 4415439177929696255004563)
    ·
      refine ⟨6623158766894544382506845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4415439177929696255004563 6623158766894544382506845)
      ·
        refine ⟨2483684537585454143440067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6623158766894544382506845 2483684537585454143440067)
        ·
          refine ⟨3725526806378181215160101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483684537585454143440067 3725526806378181215160101)
          ·
            refine ⟨698536276195908977842519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3725526806378181215160101 698536276195908977842519)
            ·
              refine ⟨1047804414293863466763779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698536276195908977842519 1047804414293863466763779)
              ·
                refine ⟨1571706621440795200145669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047804414293863466763779 1571706621440795200145669)
                ·
                  refine ⟨294694991520149100027313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571706621440795200145669 294694991520149100027313)
                  ·
                    refine ⟨221021243640111825020485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294694991520149100027313 221021243640111825020485)
                    ·
                      refine ⟨41441483182520967191341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 221021243640111825020485 41441483182520967191341)
                      ·
                        rfl

theorem cell23_80707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_80707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80707 prefixEnd_80707 := by exact prefixLift 80707
  have htrace : WordTrace (prefixWord ++ tailWord_80707) baseStart_80707 baseEnd_80707 := by
    simpa [prefixWord, tailWord_80707, baseEnd_80707] using wordTrace_append hprefix tailTrace_80707
  have hstable : (prefixWord ++ tailWord_80707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80707).length < 2 ^ (prefixWord ++ tailWord_80707).sum := by decide
  have hdescent : baseEnd_80707 < baseStart_80707 := by decide
  rcases family_descends (prefixWord ++ tailWord_80707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80747 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 1, 7]
def baseStart_80747 : Nat := 118140960795 + 80747 * 2 ^ 59
def prefixEnd_80747 : Nat := 4983230072969 + 3 ^ 40 * 80747 * 2
def baseEnd_80747 : Nat := 13820674136233603563719

theorem tailTrace_80747 : CollatzResearch.WordTrace tailWord_80747 prefixEnd_80747 13820674136233603563719 := by
  unfold tailWord_80747
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945085038474884334792495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1963390025649922889861663 2945085038474884334792495)
  ·
    refine ⟨4417627557712326502188743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2945085038474884334792495 4417627557712326502188743)
    ·
      refine ⟨6626441336568489753283115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4417627557712326502188743 6626441336568489753283115)
      ·
        refine ⟨9939662004852734629924673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6626441336568489753283115 9939662004852734629924673)
        ·
          refine ⟨7454746503639550972443505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9939662004852734629924673 7454746503639550972443505)
          ·
            refine ⟨5591059877729663229332629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454746503639550972443505 5591059877729663229332629)
            ·
              refine ⟨262080931768577963874967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5591059877729663229332629 262080931768577963874967)
              ·
                refine ⟨393121397652866945812451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262080931768577963874967 393121397652866945812451)
                ·
                  refine ⟨589682096479300418718677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 393121397652866945812451 589682096479300418718677)
                  ·
                    refine ⟨13820674136233603563719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 589682096479300418718677 13820674136233603563719)
                    ·
                      rfl

theorem cell23_80747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_80747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80747 prefixEnd_80747 := by exact prefixLift 80747
  have htrace : WordTrace (prefixWord ++ tailWord_80747) baseStart_80747 baseEnd_80747 := by
    simpa [prefixWord, tailWord_80747, baseEnd_80747] using wordTrace_append hprefix tailTrace_80747
  have hstable : (prefixWord ++ tailWord_80747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80747).length < 2 ^ (prefixWord ++ tailWord_80747).sum := by decide
  have hdescent : baseEnd_80747 < baseStart_80747 := by decide
  rcases family_descends (prefixWord ++ tailWord_80747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80801 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_80801 : Nat := 118140960795 + 80801 * 2 ^ 59
def prefixEnd_80801 : Nat := 4983230072969 + 3 ^ 40 * 80801 * 2
def baseEnd_80801 : Nat := 41489750364043599415909

theorem tailTrace_80801 : CollatzResearch.WordTrace tailWord_80801 prefixEnd_80801 41489750364043599415909 := by
  unfold tailWord_80801
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947054580279251557258257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1964703053519501038172171 2947054580279251557258257)
  ·
    refine ⟨2210290935209438667943693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2947054580279251557258257 2210290935209438667943693)
    ·
      refine ⟨828859100703539500478885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2210290935209438667943693 828859100703539500478885)
      ·
        refine ⟨155411081381913656339791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 828859100703539500478885 155411081381913656339791)
        ·
          refine ⟨233116622072870484509687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155411081381913656339791 233116622072870484509687)
          ·
            refine ⟨349674933109305726764531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233116622072870484509687 349674933109305726764531)
            ·
              refine ⟨524512399663958590146797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349674933109305726764531 524512399663958590146797)
              ·
                refine ⟨196692149873984471305049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524512399663958590146797 196692149873984471305049)
                ·
                  refine ⟨147519112405488353478787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196692149873984471305049 147519112405488353478787)
                  ·
                    refine ⟨221278668608232530218181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147519112405488353478787 221278668608232530218181)
                    ·
                      refine ⟨41489750364043599415909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 221278668608232530218181 41489750364043599415909)
                      ·
                        rfl

theorem cell23_80801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_80801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80801 prefixEnd_80801 := by exact prefixLift 80801
  have htrace : WordTrace (prefixWord ++ tailWord_80801) baseStart_80801 baseEnd_80801 := by
    simpa [prefixWord, tailWord_80801, baseEnd_80801] using wordTrace_append hprefix tailTrace_80801
  have hstable : (prefixWord ++ tailWord_80801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80801).length < 2 ^ (prefixWord ++ tailWord_80801).sum := by decide
  have hdescent : baseEnd_80801 < baseStart_80801 := by decide
  rcases family_descends (prefixWord ++ tailWord_80801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80821 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_80821 : Nat := 118140960795 + 80821 * 2 ^ 59
def prefixEnd_80821 : Nat := 4983230072969 + 3 ^ 40 * 80821 * 2
def baseEnd_80821 : Nat := 41500019977133521165817

theorem tailTrace_80821 : CollatzResearch.WordTrace tailWord_80821 prefixEnd_80821 41500019977133521165817 := by
  unfold tailWord_80821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947784040206794972986317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1965189360137863315324211 2947784040206794972986317)
  ·
    refine ⟨1105419015077548114869869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2947784040206794972986317 1105419015077548114869869)
    ·
      refine ⟨414532130654080543076201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1105419015077548114869869 414532130654080543076201)
      ·
        refine ⟨310899097990560407307151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414532130654080543076201 310899097990560407307151)
        ·
          refine ⟨466348646985840610960727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310899097990560407307151 466348646985840610960727)
          ·
            refine ⟨699522970478760916441091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466348646985840610960727 699522970478760916441091)
            ·
              refine ⟨1049284455718141374661637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699522970478760916441091 1049284455718141374661637)
              ·
                refine ⟨196740835447151507749057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1049284455718141374661637 196740835447151507749057)
                ·
                  refine ⟨147555626585363630811793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196740835447151507749057 147555626585363630811793)
                  ·
                    refine ⟨110666719939022723108845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147555626585363630811793 110666719939022723108845)
                    ·
                      refine ⟨41500019977133521165817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110666719939022723108845 41500019977133521165817)
                      ·
                        rfl

theorem cell23_80821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_80821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80821 prefixEnd_80821 := by exact prefixLift 80821
  have htrace : WordTrace (prefixWord ++ tailWord_80821) baseStart_80821 baseEnd_80821 := by
    simpa [prefixWord, tailWord_80821, baseEnd_80821] using wordTrace_append hprefix tailTrace_80821
  have hstable : (prefixWord ++ tailWord_80821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80821).length < 2 ^ (prefixWord ++ tailWord_80821).sum := by decide
  have hdescent : baseEnd_80821 < baseStart_80821 := by decide
  rcases family_descends (prefixWord ++ tailWord_80821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80824 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 6]
def baseStart_80824 : Nat := 118140960795 + 80824 * 2 ^ 59
def prefixEnd_80824 : Nat := 4983230072969 + 3 ^ 40 * 80824 * 2
def baseEnd_80824 : Nat := 4611284491010778825367

theorem tailTrace_80824 : CollatzResearch.WordTrace tailWord_80824 prefixEnd_80824 4611284491010778825367 := by
  unfold tailWord_80824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473946729597963242672763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1965262306130617656897017 1473946729597963242672763)
  ·
    refine ⟨2210920094396944864009145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473946729597963242672763 2210920094396944864009145)
    ·
      refine ⟨1658190070797708648006859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2210920094396944864009145 1658190070797708648006859)
      ·
        refine ⟨2487285106196562972010289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658190070797708648006859 2487285106196562972010289)
        ·
          refine ⟨1865463829647422229007717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2487285106196562972010289 1865463829647422229007717)
          ·
            refine ⟨349774468058891667938947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1865463829647422229007717 349774468058891667938947)
            ·
              refine ⟨524661702088337501908421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349774468058891667938947 524661702088337501908421)
              ·
                refine ⟨98374069141563281607829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524661702088337501908421 98374069141563281607829)
                ·
                  refine ⟨4611284491010778825367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98374069141563281607829 4611284491010778825367)
                  ·
                    rfl

theorem cell23_80824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 6].length) (baseStart_80824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80824 prefixEnd_80824 := by exact prefixLift 80824
  have htrace : WordTrace (prefixWord ++ tailWord_80824) baseStart_80824 baseEnd_80824 := by
    simpa [prefixWord, tailWord_80824, baseEnd_80824] using wordTrace_append hprefix tailTrace_80824
  have hstable : (prefixWord ++ tailWord_80824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80824).length < 2 ^ (prefixWord ++ tailWord_80824).sum := by decide
  have hdescent : baseEnd_80824 < baseStart_80824 := by decide
  rcases family_descends (prefixWord ++ tailWord_80824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80908 : List Nat := [2, 2, 1, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_80908 : Nat := 118140960795 + 80908 * 2 ^ 59
def prefixEnd_80908 : Nat := 4983230072969 + 3 ^ 40 * 80908 * 2
def baseEnd_80908 : Nat := 41544692794074680777917

theorem tailTrace_80908 : CollatzResearch.WordTrace tailWord_80908 prefixEnd_80908 41544692794074680777917 := by
  unfold tailWord_80908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475478595445804415701689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1967304793927739220935585 1475478595445804415701689)
  ·
    refine ⟨1106608946584353311776267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1475478595445804415701689 1106608946584353311776267)
    ·
      refine ⟨1659913419876529967664401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106608946584353311776267 1659913419876529967664401)
      ·
        refine ⟨1244935064907397475748301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659913419876529967664401 1244935064907397475748301)
        ·
          refine ⟨466850649340274053405613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1244935064907397475748301 466850649340274053405613)
          ·
            refine ⟨175068993502602770027105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 466850649340274053405613 175068993502602770027105)
            ·
              refine ⟨131301745126952077520329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175068993502602770027105 131301745126952077520329)
              ·
                refine ⟨98476308845214058140247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131301745126952077520329 98476308845214058140247)
                ·
                  refine ⟨147714463267821087210371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98476308845214058140247 147714463267821087210371)
                  ·
                    refine ⟨221571694901731630815557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147714463267821087210371 221571694901731630815557)
                    ·
                      refine ⟨41544692794074680777917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 221571694901731630815557 41544692794074680777917)
                      ·
                        rfl

theorem cell23_80908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_80908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80908 prefixEnd_80908 := by exact prefixLift 80908
  have htrace : WordTrace (prefixWord ++ tailWord_80908) baseStart_80908 baseEnd_80908 := by
    simpa [prefixWord, tailWord_80908, baseEnd_80908] using wordTrace_append hprefix tailTrace_80908
  have hstable : (prefixWord ++ tailWord_80908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80908).length < 2 ^ (prefixWord ++ tailWord_80908).sum := by decide
  have hdescent : baseEnd_80908 < baseStart_80908 := by decide
  rcases family_descends (prefixWord ++ tailWord_80908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80944 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_80944 : Nat := 118140960795 + 80944 * 2 ^ 59
def prefixEnd_80944 : Nat := 4983230072969 + 3 ^ 40 * 80944 * 2
def baseEnd_80944 : Nat := 13854392699212179975917

theorem tailTrace_80944 : CollatzResearch.WordTrace tailWord_80944 prefixEnd_80944 13854392699212179975917 := by
  unfold tailWord_80944
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476135109380593489856943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1968180145840791319809257 1476135109380593489856943)
  ·
    refine ⟨2214202664070890234785415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1476135109380593489856943 2214202664070890234785415)
    ·
      refine ⟨3321303996106335352178123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214202664070890234785415 3321303996106335352178123)
      ·
        refine ⟨4981955994159503028267185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321303996106335352178123 4981955994159503028267185)
        ·
          refine ⟨3736466995619627271200389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4981955994159503028267185 3736466995619627271200389)
          ·
            refine ⟨700587561678680113350073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3736466995619627271200389 700587561678680113350073)
            ·
              refine ⟨525440671259010085012555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700587561678680113350073 525440671259010085012555)
              ·
                refine ⟨788161006888515127518833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525440671259010085012555 788161006888515127518833)
                ·
                  refine ⟨591120755166386345639125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788161006888515127518833 591120755166386345639125)
                  ·
                    refine ⟨13854392699212179975917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 591120755166386345639125 13854392699212179975917)
                    ·
                      rfl

theorem cell23_80944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_80944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80944 prefixEnd_80944 := by exact prefixLift 80944
  have htrace : WordTrace (prefixWord ++ tailWord_80944) baseStart_80944 baseEnd_80944 := by
    simpa [prefixWord, tailWord_80944, baseEnd_80944] using wordTrace_append hprefix tailTrace_80944
  have hstable : (prefixWord ++ tailWord_80944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80944).length < 2 ^ (prefixWord ++ tailWord_80944).sum := by decide
  have hdescent : baseEnd_80944 < baseStart_80944 := by decide
  rcases family_descends (prefixWord ++ tailWord_80944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80948 : List Nat := [2, 5, 1, 2, 1, 2, 2, 8]
def baseStart_80948 : Nat := 118140960795 + 80948 * 2 ^ 59
def prefixEnd_80948 : Nat := 4983230072969 + 3 ^ 40 * 80948 * 2
def baseEnd_80948 : Nat := 1539453037787204602879

theorem tailTrace_80948 : CollatzResearch.WordTrace tailWord_80948 prefixEnd_80948 1539453037787204602879 := by
  unfold tailWord_80948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476208055373347831429749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1968277407164463775239665 1476208055373347831429749)
  ·
    refine ⟨138394505191251359196539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1476208055373347831429749 138394505191251359196539)
    ·
      refine ⟨207591757786877038794809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138394505191251359196539 207591757786877038794809)
      ·
        refine ⟨155693818340157779096107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207591757786877038794809 155693818340157779096107)
        ·
          refine ⟨233540727510236668644161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155693818340157779096107 233540727510236668644161)
          ·
            refine ⟨175155545632677501483121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233540727510236668644161 175155545632677501483121)
            ·
              refine ⟨131366659224508126112341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175155545632677501483121 131366659224508126112341)
              ·
                refine ⟨1539453037787204602879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 131366659224508126112341 1539453037787204602879)
                ·
                  rfl

theorem cell23_80948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 8].length) (baseStart_80948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80948 prefixEnd_80948 := by exact prefixLift 80948
  have htrace : WordTrace (prefixWord ++ tailWord_80948) baseStart_80948 baseEnd_80948 := by
    simpa [prefixWord, tailWord_80948, baseEnd_80948] using wordTrace_append hprefix tailTrace_80948
  have hstable : (prefixWord ++ tailWord_80948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80948).length < 2 ^ (prefixWord ++ tailWord_80948).sum := by decide
  have hdescent : baseEnd_80948 < baseStart_80948 := by decide
  rcases family_descends (prefixWord ++ tailWord_80948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80951 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 7, 2]
def baseStart_80951 : Nat := 118140960795 + 80951 * 2 ^ 59
def prefixEnd_80951 : Nat := 4983230072969 + 3 ^ 40 * 80951 * 2
def baseEnd_80951 : Nat := 41566772462218012540219

theorem tailTrace_80951 : CollatzResearch.WordTrace tailWord_80951 prefixEnd_80951 41566772462218012540219 := by
  unfold tailWord_80951
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952525529735827175218707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1968350353157218116812471 2952525529735827175218707)
  ·
    refine ⟨4428788294603740762828061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2952525529735827175218707 4428788294603740762828061)
    ·
      refine ⟨1660795610476402786060523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4428788294603740762828061 1660795610476402786060523)
      ·
        refine ⟨2491193415714604179090785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660795610476402786060523 2491193415714604179090785)
        ·
          refine ⟨1868395061785953134318089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491193415714604179090785 1868395061785953134318089)
          ·
            refine ⟨1401296296339464850738567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868395061785953134318089 1401296296339464850738567)
            ·
              refine ⟨2101944444509197276107851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401296296339464850738567 2101944444509197276107851)
              ·
                refine ⟨3152916666763795914161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2101944444509197276107851 3152916666763795914161777)
                ·
                  refine ⟨2364687500072846935621333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3152916666763795914161777 2364687500072846935621333)
                  ·
                    refine ⟨55422363282957350053625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2364687500072846935621333 55422363282957350053625)
                    ·
                      refine ⟨41566772462218012540219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55422363282957350053625 41566772462218012540219)
                      ·
                        rfl

theorem cell23_80951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_80951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80951 prefixEnd_80951 := by exact prefixLift 80951
  have htrace : WordTrace (prefixWord ++ tailWord_80951) baseStart_80951 baseEnd_80951 := by
    simpa [prefixWord, tailWord_80951, baseEnd_80951] using wordTrace_append hprefix tailTrace_80951
  have hstable : (prefixWord ++ tailWord_80951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80951).length < 2 ^ (prefixWord ++ tailWord_80951).sum := by decide
  have hdescent : baseEnd_80951 < baseStart_80951 := by decide
  rcases family_descends (prefixWord ++ tailWord_80951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80968 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_80968 : Nat := 118140960795 + 80968 * 2 ^ 59
def prefixEnd_80968 : Nat := 4983230072969 + 3 ^ 40 * 80968 * 2
def baseEnd_80968 : Nat := 41575501633344446027641

theorem tailTrace_80968 : CollatzResearch.WordTrace tailWord_80968 prefixEnd_80968 41575501633344446027641 := by
  unfold tailWord_80968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476572785337119539293779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1968763713782826052391705 1476572785337119539293779)
  ·
    refine ⟨2214859178005679308940669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1476572785337119539293779 2214859178005679308940669)
    ·
      refine ⟨830572191752129740852751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2214859178005679308940669 830572191752129740852751)
      ·
        refine ⟨1245858287628194611279127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830572191752129740852751 1245858287628194611279127)
        ·
          refine ⟨1868787431442291916918691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245858287628194611279127 1868787431442291916918691)
          ·
            refine ⟨2803181147163437875378037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868787431442291916918691 2803181147163437875378037)
            ·
              refine ⟨262798232546572300816691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2803181147163437875378037 262798232546572300816691)
              ·
                refine ⟨394197348819858451225037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262798232546572300816691 394197348819858451225037)
                ·
                  refine ⟨147824005807446919209389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394197348819858451225037 147824005807446919209389)
                  ·
                    refine ⟨55434002177792594703521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 147824005807446919209389 55434002177792594703521)
                    ·
                      refine ⟨41575501633344446027641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55434002177792594703521 41575501633344446027641)
                      ·
                        rfl

theorem cell23_80968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_80968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_80968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_80968 prefixEnd_80968 := by exact prefixLift 80968
  have htrace : WordTrace (prefixWord ++ tailWord_80968) baseStart_80968 baseEnd_80968 := by
    simpa [prefixWord, tailWord_80968, baseEnd_80968] using wordTrace_append hprefix tailTrace_80968
  have hstable : (prefixWord ++ tailWord_80968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80968).length < 2 ^ (prefixWord ++ tailWord_80968).sum := by decide
  have hdescent : baseEnd_80968 < baseStart_80968 := by decide
  rcases family_descends (prefixWord ++ tailWord_80968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81001 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_81001 : Nat := 118140960795 + 81001 * 2 ^ 59
def prefixEnd_81001 : Nat := 4983230072969 + 3 ^ 40 * 81001 * 2
def baseEnd_81001 : Nat := 41592446494942816914989

theorem tailTrace_81001 : CollatzResearch.WordTrace tailWord_81001 prefixEnd_81001 41592446494942816914989 := by
  unfold tailWord_81001
  simp only [CollatzResearch.WordTrace]
  refine ⟨2954349179554685714538857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1969566119703123809692571 2954349179554685714538857)
  ·
    refine ⟨2215761884666014285904143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2954349179554685714538857 2215761884666014285904143)
    ·
      refine ⟨3323642826999021428856215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215761884666014285904143 3323642826999021428856215)
      ·
        refine ⟨4985464240498532143284323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323642826999021428856215 4985464240498532143284323)
        ·
          refine ⟨7478196360747798214926485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4985464240498532143284323 7478196360747798214926485)
          ·
            refine ⟨350540454410053041324679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7478196360747798214926485 350540454410053041324679)
            ·
              refine ⟨525810681615079561987019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350540454410053041324679 525810681615079561987019)
              ·
                refine ⟨788716022422619342980529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525810681615079561987019 788716022422619342980529)
                ·
                  refine ⟨591537016816964507235397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788716022422619342980529 591537016816964507235397)
                  ·
                    refine ⟨110913190653180845106637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591537016816964507235397 110913190653180845106637)
                    ·
                      refine ⟨41592446494942816914989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110913190653180845106637 41592446494942816914989)
                      ·
                        rfl

theorem cell23_81001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_81001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81001 prefixEnd_81001 := by exact prefixLift 81001
  have htrace : WordTrace (prefixWord ++ tailWord_81001) baseStart_81001 baseEnd_81001 := by
    simpa [prefixWord, tailWord_81001, baseEnd_81001] using wordTrace_append hprefix tailTrace_81001
  have hstable : (prefixWord ++ tailWord_81001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81001).length < 2 ^ (prefixWord ++ tailWord_81001).sum := by decide
  have hdescent : baseEnd_81001 < baseStart_81001 := by decide
  rcases family_descends (prefixWord ++ tailWord_81001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81015 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 2, 2, 2]
def baseStart_81015 : Nat := 118140960795 + 81015 * 2 ^ 59
def prefixEnd_81015 : Nat := 4983230072969 + 3 ^ 40 * 81015 * 2
def baseEnd_81015 : Nat := 41599635224105762139925

theorem tailTrace_81015 : CollatzResearch.WordTrace tailWord_81015 prefixEnd_81015 41599635224105762139925 := by
  unfold tailWord_81015
  simp only [CollatzResearch.WordTrace]
  refine ⟨2954859801503966105548499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1969906534335977403698999 2954859801503966105548499)
  ·
    refine ⟨4432289702255949158322749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2954859801503966105548499 4432289702255949158322749)
    ·
      refine ⟨1662108638345980934371031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4432289702255949158322749 1662108638345980934371031)
      ·
        refine ⟨2493162957518971401556547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662108638345980934371031 2493162957518971401556547)
        ·
          refine ⟨3739744436278457102334821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493162957518971401556547 3739744436278457102334821)
          ·
            refine ⟨701202081802210706687779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3739744436278457102334821 701202081802210706687779)
            ·
              refine ⟨1051803122703316060031669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701202081802210706687779 1051803122703316060031669)
              ·
                refine ⟨98606542753435880627969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1051803122703316060031669 98606542753435880627969)
                ·
                  refine ⟨73954907065076910470977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98606542753435880627969 73954907065076910470977)
                  ·
                    refine ⟨55466180298807682853233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73954907065076910470977 55466180298807682853233)
                    ·
                      refine ⟨41599635224105762139925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55466180298807682853233 41599635224105762139925)
                      ·
                        rfl

theorem cell23_81015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_81015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81015 prefixEnd_81015 := by exact prefixLift 81015
  have htrace : WordTrace (prefixWord ++ tailWord_81015) baseStart_81015 baseEnd_81015 := by
    simpa [prefixWord, tailWord_81015, baseEnd_81015] using wordTrace_append hprefix tailTrace_81015
  have hstable : (prefixWord ++ tailWord_81015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81015).length < 2 ^ (prefixWord ++ tailWord_81015).sum := by decide
  have hdescent : baseEnd_81015 < baseStart_81015 := by decide
  rcases family_descends (prefixWord ++ tailWord_81015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81021 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 7]
def baseStart_81021 : Nat := 118140960795 + 81021 * 2 ^ 59
def prefixEnd_81021 : Nat := 4983230072969 + 3 ^ 40 * 81021 * 2
def baseEnd_81021 : Nat := 4622524012003637629433

theorem tailTrace_81021 : CollatzResearch.WordTrace tailWord_81021 prefixEnd_81021 4622524012003637629433 := by
  unfold tailWord_81021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955078639482229130266917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1970052426321486086844611 2955078639482229130266917)
  ·
    refine ⟨554077244902917961925047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2955078639482229130266917 554077244902917961925047)
    ·
      refine ⟨831115867354376942887571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554077244902917961925047 831115867354376942887571)
      ·
        refine ⟨1246673801031565414331357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831115867354376942887571 1246673801031565414331357)
        ·
          refine ⟨467502675386837030374259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1246673801031565414331357 467502675386837030374259)
          ·
            refine ⟨701254013080255545561389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467502675386837030374259 701254013080255545561389)
            ·
              refine ⟨262970254905095829585521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701254013080255545561389 262970254905095829585521)
              ·
                refine ⟨197227691178821872189141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262970254905095829585521 197227691178821872189141)
                ·
                  refine ⟨4622524012003637629433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197227691178821872189141 4622524012003637629433)
                  ·
                    rfl

theorem cell23_81021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_81021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81021 prefixEnd_81021 := by exact prefixLift 81021
  have htrace : WordTrace (prefixWord ++ tailWord_81021) baseStart_81021 baseEnd_81021 := by
    simpa [prefixWord, tailWord_81021, baseEnd_81021] using wordTrace_append hprefix tailTrace_81021
  have hstable : (prefixWord ++ tailWord_81021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81021).length < 2 ^ (prefixWord ++ tailWord_81021).sum := by decide
  have hdescent : baseEnd_81021 < baseStart_81021 := by decide
  rcases family_descends (prefixWord ++ tailWord_81021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81031 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_81031 : Nat := 118140960795 + 81031 * 2 ^ 59
def prefixEnd_81031 : Nat := 4983230072969 + 3 ^ 40 * 81031 * 2
def baseEnd_81031 : Nat := 41607850914577699539851

theorem tailTrace_81031 : CollatzResearch.WordTrace tailWord_81031 prefixEnd_81031 41607850914577699539851 := by
  unfold tailWord_81031
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955443369446000838130947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1970295579630667225420631 2955443369446000838130947)
  ·
    refine ⟨4433165054169001257196421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955443369446000838130947 4433165054169001257196421)
    ·
      refine ⟨831218447656687735724329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4433165054169001257196421 831218447656687735724329)
      ·
        refine ⟨623413835742515801793247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 831218447656687735724329 623413835742515801793247)
        ·
          refine ⟨935120753613773702689871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623413835742515801793247 935120753613773702689871)
          ·
            refine ⟨1402681130420660554034807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935120753613773702689871 1402681130420660554034807)
            ·
              refine ⟨2104021695630990831052211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402681130420660554034807 2104021695630990831052211)
              ·
                refine ⟨3156032543446486246578317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104021695630990831052211 3156032543446486246578317)
                ·
                  refine ⟨1183512203792432342466869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3156032543446486246578317 1183512203792432342466869)
                  ·
                    refine ⟨110954269105540532106269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1183512203792432342466869 110954269105540532106269)
                    ·
                      refine ⟨41607850914577699539851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110954269105540532106269 41607850914577699539851)
                      ·
                        rfl

theorem cell23_81031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_81031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81031 prefixEnd_81031 := by exact prefixLift 81031
  have htrace : WordTrace (prefixWord ++ tailWord_81031) baseStart_81031 baseEnd_81031 := by
    simpa [prefixWord, tailWord_81031, baseEnd_81031] using wordTrace_append hprefix tailTrace_81031
  have hstable : (prefixWord ++ tailWord_81031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81031).length < 2 ^ (prefixWord ++ tailWord_81031).sum := by decide
  have hdescent : baseEnd_81031 < baseStart_81031 := by decide
  rcases family_descends (prefixWord ++ tailWord_81031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81048 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_81048 : Nat := 118140960795 + 81048 * 2 ^ 59
def prefixEnd_81048 : Nat := 4983230072969 + 3 ^ 40 * 81048 * 2
def baseEnd_81048 : Nat := 41616580085704133027273

theorem tailTrace_81048 : CollatzResearch.WordTrace tailWord_81048 prefixEnd_81048 41616580085704133027273 := by
  unfold tailWord_81048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478031705192206370749899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1970708940256275160999865 1478031705192206370749899)
  ·
    refine ⟨2217047557788309556124849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1478031705192206370749899 2217047557788309556124849)
    ·
      refine ⟨1662785668341232167093637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2217047557788309556124849 1662785668341232167093637)
      ·
        refine ⟨311772312813981031330057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1662785668341232167093637 311772312813981031330057)
        ·
          refine ⟨233829234610485773497543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311772312813981031330057 233829234610485773497543)
          ·
            refine ⟨350743851915728660246315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233829234610485773497543 350743851915728660246315)
            ·
              refine ⟨526115777873592990369473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350743851915728660246315 526115777873592990369473)
              ·
                refine ⟨394586833405194742777105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526115777873592990369473 394586833405194742777105)
                ·
                  refine ⟨295940125053896057082829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394586833405194742777105 295940125053896057082829)
                  ·
                    refine ⟨110977546895211021406061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295940125053896057082829 110977546895211021406061)
                    ·
                      refine ⟨41616580085704133027273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 110977546895211021406061 41616580085704133027273)
                      ·
                        rfl

theorem cell23_81048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_81048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81048 prefixEnd_81048 := by exact prefixLift 81048
  have htrace : WordTrace (prefixWord ++ tailWord_81048) baseStart_81048 baseEnd_81048 := by
    simpa [prefixWord, tailWord_81048, baseEnd_81048] using wordTrace_append hprefix tailTrace_81048
  have hstable : (prefixWord ++ tailWord_81048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81048).length < 2 ^ (prefixWord ++ tailWord_81048).sum := by decide
  have hdescent : baseEnd_81048 < baseStart_81048 := by decide
  rcases family_descends (prefixWord ++ tailWord_81048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81066 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_81066 : Nat := 118140960795 + 81066 * 2 ^ 59
def prefixEnd_81066 : Nat := 4983230072969 + 3 ^ 40 * 81066 * 2
def baseEnd_81066 : Nat := 41625822737485062602191

theorem tailTrace_81066 : CollatzResearch.WordTrace tailWord_81066 prefixEnd_81066 41625822737485062602191 := by
  unfold tailWord_81066
  simp only [CollatzResearch.WordTrace]
  refine ⟨739179981079800453913763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1971146616212801210436701 739179981079800453913763)
  ·
    refine ⟨1108769971619700680870645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739179981079800453913763 1108769971619700680870645)
    ·
      refine ⟨103947184839346938831623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1108769971619700680870645 103947184839346938831623)
      ·
        refine ⟨155920777259020408247435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103947184839346938831623 155920777259020408247435)
        ·
          refine ⟨233881165888530612371153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155920777259020408247435 233881165888530612371153)
          ·
            refine ⟨175410874416397959278365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233881165888530612371153 175410874416397959278365)
            ·
              refine ⟨65779077906149234729387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175410874416397959278365 65779077906149234729387)
              ·
                refine ⟨98668616859223852094081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65779077906149234729387 98668616859223852094081)
                ·
                  refine ⟨74001462644417889070561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98668616859223852094081 74001462644417889070561)
                  ·
                    refine ⟨55501096983313416802921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74001462644417889070561 55501096983313416802921)
                    ·
                      refine ⟨41625822737485062602191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55501096983313416802921 41625822737485062602191)
                      ·
                        rfl

theorem cell23_81066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_81066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81066 prefixEnd_81066 := by exact prefixLift 81066
  have htrace : WordTrace (prefixWord ++ tailWord_81066) baseStart_81066 baseEnd_81066 := by
    simpa [prefixWord, tailWord_81066, baseEnd_81066] using wordTrace_append hprefix tailTrace_81066
  have hstable : (prefixWord ++ tailWord_81066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81066).length < 2 ^ (prefixWord ++ tailWord_81066).sum := by decide
  have hdescent : baseEnd_81066 < baseStart_81066 := by decide
  rcases family_descends (prefixWord ++ tailWord_81066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81071 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_81071 : Nat := 118140960795 + 81071 * 2 ^ 59
def prefixEnd_81071 : Nat := 4983230072969 + 3 ^ 40 * 81071 * 2
def baseEnd_81071 : Nat := 41628390140757543039667

theorem tailTrace_81071 : CollatzResearch.WordTrace tailWord_81071 prefixEnd_81071 41628390140757543039667 := by
  unfold tailWord_81071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956902289301087669587067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1971268192867391779724711 2956902289301087669587067)
  ·
    refine ⟨4435353433951631504380601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2956902289301087669587067 4435353433951631504380601)
    ·
      refine ⟨3326515075463723628285451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4435353433951631504380601 3326515075463723628285451)
      ·
        refine ⟨4989772613195585442428177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326515075463723628285451 4989772613195585442428177)
        ·
          refine ⟨3742329459896689081821133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4989772613195585442428177 3742329459896689081821133)
          ·
            refine ⟨1403373547461258405682925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3742329459896689081821133 1403373547461258405682925)
            ·
              refine ⟨526265080297971902131097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403373547461258405682925 526265080297971902131097)
              ·
                refine ⟨394698810223478926598323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526265080297971902131097 394698810223478926598323)
                ·
                  refine ⟨592048215335218389897485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394698810223478926598323 592048215335218389897485)
                  ·
                    refine ⟨222018080750706896211557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592048215335218389897485 222018080750706896211557)
                    ·
                      refine ⟨41628390140757543039667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 222018080750706896211557 41628390140757543039667)
                      ·
                        rfl

theorem cell23_81071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_81071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81071 prefixEnd_81071 := by exact prefixLift 81071
  have htrace : WordTrace (prefixWord ++ tailWord_81071) baseStart_81071 baseEnd_81071 := by
    simpa [prefixWord, tailWord_81071, baseEnd_81071] using wordTrace_append hprefix tailTrace_81071
  have hstable : (prefixWord ++ tailWord_81071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81071).length < 2 ^ (prefixWord ++ tailWord_81071).sum := by decide
  have hdescent : baseEnd_81071 < baseStart_81071 := by decide
  rcases family_descends (prefixWord ++ tailWord_81071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81111 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 8]
def baseStart_81111 : Nat := 118140960795 + 81111 * 2 ^ 59
def prefixEnd_81111 : Nat := 4983230072969 + 3 ^ 40 * 81111 * 2
def baseEnd_81111 : Nat := 4627658818548598504387

theorem tailTrace_81111 : CollatzResearch.WordTrace tailWord_81111 prefixEnd_81111 4627658818548598504387 := by
  unfold tailWord_81111
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958361209156174501043187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1972240806104116334028791 2958361209156174501043187)
  ·
    refine ⟨4437541813734261751564781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2958361209156174501043187 4437541813734261751564781)
    ·
      refine ⟨1664078180150348156836793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4437541813734261751564781 1664078180150348156836793)
      ·
        refine ⟨1248058635112761117627595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664078180150348156836793 1248058635112761117627595)
        ·
          refine ⟨1872087952669141676441393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248058635112761117627595 1872087952669141676441393)
          ·
            refine ⟨1404065964501856257331045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872087952669141676441393 1404065964501856257331045)
            ·
              refine ⟨263262368344098048249571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1404065964501856257331045 263262368344098048249571)
              ·
                refine ⟨394893552516147072374357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263262368344098048249571 394893552516147072374357)
                ·
                  refine ⟨4627658818548598504387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 394893552516147072374357 4627658818548598504387)
                  ·
                    rfl

theorem cell23_81111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 8].length) (baseStart_81111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81111 prefixEnd_81111 := by exact prefixLift 81111
  have htrace : WordTrace (prefixWord ++ tailWord_81111) baseStart_81111 baseEnd_81111 := by
    simpa [prefixWord, tailWord_81111, baseEnd_81111] using wordTrace_append hprefix tailTrace_81111
  have hstable : (prefixWord ++ tailWord_81111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81111).length < 2 ^ (prefixWord ++ tailWord_81111).sum := by decide
  have hdescent : baseEnd_81111 < baseStart_81111 := by decide
  rcases family_descends (prefixWord ++ tailWord_81111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81128 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 6]
def baseStart_81128 : Nat := 118140960795 + 81128 * 2 ^ 59
def prefixEnd_81128 : Nat := 4983230072969 + 3 ^ 40 * 81128 * 2
def baseEnd_81128 : Nat := 4628628726451535558545

theorem tailTrace_81128 : CollatzResearch.WordTrace tailWord_81128 prefixEnd_81128 4628628726451535558545 := by
  unfold tailWord_81128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479490625047293202206019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1972654166729724269608025 1479490625047293202206019)
  ·
    refine ⟨2219235937570939803309029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1479490625047293202206019 2219235937570939803309029)
    ·
      refine ⟨416106738294551213120443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2219235937570939803309029 416106738294551213120443)
      ·
        refine ⟨624160107441826819680665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416106738294551213120443 624160107441826819680665)
        ·
          refine ⟨468120080581370114760499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624160107441826819680665 468120080581370114760499)
          ·
            refine ⟨702180120872055172140749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468120080581370114760499 702180120872055172140749)
            ·
              refine ⟨263317545327020689552781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 702180120872055172140749 263317545327020689552781)
              ·
                refine ⟨98744079497632758582293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263317545327020689552781 98744079497632758582293)
                ·
                  refine ⟨4628628726451535558545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98744079497632758582293 4628628726451535558545)
                  ·
                    rfl

theorem cell23_81128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 6].length) (baseStart_81128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81128 prefixEnd_81128 := by exact prefixLift 81128
  have htrace : WordTrace (prefixWord ++ tailWord_81128) baseStart_81128 baseEnd_81128 := by
    simpa [prefixWord, tailWord_81128, baseEnd_81128] using wordTrace_append hprefix tailTrace_81128
  have hstable : (prefixWord ++ tailWord_81128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81128).length < 2 ^ (prefixWord ++ tailWord_81128).sum := by decide
  have hdescent : baseEnd_81128 < baseStart_81128 := by decide
  rcases family_descends (prefixWord ++ tailWord_81128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81209 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 1, 5]
def baseStart_81209 : Nat := 118140960795 + 81209 * 2 ^ 59
def prefixEnd_81209 : Nat := 4983230072969 + 3 ^ 40 * 81209 * 2
def baseEnd_81209 : Nat := 13899750157026001038011

theorem tailTrace_81209 : CollatzResearch.WordTrace tailWord_81209 prefixEnd_81209 13899750157026001038011 := by
  unfold tailWord_81209
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961935562801137238110681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1974623708534091492073787 2961935562801137238110681)
  ·
    refine ⟨2221451672100852928583011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2961935562801137238110681 2221451672100852928583011)
    ·
      refine ⟨3332177508151279392874517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2221451672100852928583011 3332177508151279392874517)
      ·
        refine ⟨156195820694591221540993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3332177508151279392874517 156195820694591221540993)
        ·
          refine ⟨117146865520943416155745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156195820694591221540993 117146865520943416155745)
          ·
            refine ⟨87860149140707562116809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117146865520943416155745 87860149140707562116809)
            ·
              refine ⟨65895111855530671587607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87860149140707562116809 65895111855530671587607)
              ·
                refine ⟨98842667783296007381411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65895111855530671587607 98842667783296007381411)
                ·
                  refine ⟨148264001674944011072117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98842667783296007381411 148264001674944011072117)
                  ·
                    refine ⟨13899750157026001038011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148264001674944011072117 13899750157026001038011)
                    ·
                      rfl

theorem cell23_81209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 5].length) (baseStart_81209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81209 prefixEnd_81209 := by exact prefixLift 81209
  have htrace : WordTrace (prefixWord ++ tailWord_81209) baseStart_81209 baseEnd_81209 := by
    simpa [prefixWord, tailWord_81209, baseEnd_81209] using wordTrace_append hprefix tailTrace_81209
  have hstable : (prefixWord ++ tailWord_81209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81209).length < 2 ^ (prefixWord ++ tailWord_81209).sum := by decide
  have hdescent : baseEnd_81209 < baseStart_81209 := by decide
  rcases family_descends (prefixWord ++ tailWord_81209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81211 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_81211 : Nat := 118140960795 + 81211 * 2 ^ 59
def prefixEnd_81211 : Nat := 4983230072969 + 3 ^ 40 * 81211 * 2
def baseEnd_81211 : Nat := 41700277432386995289023

theorem tailTrace_81211 : CollatzResearch.WordTrace tailWord_81211 prefixEnd_81211 41700277432386995289023 := by
  unfold tailWord_81211
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962008508793891579683487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1974672339195927719788991 2962008508793891579683487)
  ·
    refine ⟨4443012763190837369525231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962008508793891579683487 4443012763190837369525231)
    ·
      refine ⟨6664519144786256054287847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443012763190837369525231 6664519144786256054287847)
      ·
        refine ⟨9996778717179384081431771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6664519144786256054287847 9996778717179384081431771)
        ·
          refine ⟨14995168075769076122147657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9996778717179384081431771 14995168075769076122147657)
          ·
            refine ⟨11246376056826807091610743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14995168075769076122147657 11246376056826807091610743)
            ·
              refine ⟨16869564085240210637416115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11246376056826807091610743 16869564085240210637416115)
              ·
                refine ⟨25304346127860315956124173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16869564085240210637416115 25304346127860315956124173)
                ·
                  refine ⟨9489129797947618483546565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25304346127860315956124173 9489129797947618483546565)
                  ·
                    refine ⟨1779211837115178465664981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9489129797947618483546565 1779211837115178465664981)
                    ·
                      refine ⟨41700277432386995289023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1779211837115178465664981 41700277432386995289023)
                      ·
                        rfl

theorem cell23_81211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_81211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81211 prefixEnd_81211 := by exact prefixLift 81211
  have htrace : WordTrace (prefixWord ++ tailWord_81211) baseStart_81211 baseEnd_81211 := by
    simpa [prefixWord, tailWord_81211, baseEnd_81211] using wordTrace_append hprefix tailTrace_81211
  have hstable : (prefixWord ++ tailWord_81211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81211).length < 2 ^ (prefixWord ++ tailWord_81211).sum := by decide
  have hdescent : baseEnd_81211 < baseStart_81211 := by decide
  rcases family_descends (prefixWord ++ tailWord_81211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81212 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_81212 : Nat := 118140960795 + 81212 * 2 ^ 59
def prefixEnd_81212 : Nat := 4983230072969 + 3 ^ 40 * 81212 * 2
def baseEnd_81212 : Nat := 41700790913041491376519

theorem tailTrace_81212 : CollatzResearch.WordTrace tailWord_81212 prefixEnd_81212 41700790913041491376519 := by
  unfold tailWord_81212
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481022490895134375234945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1974696654526845833646593 1481022490895134375234945)
  ·
    refine ⟨1110766868171350781426209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1481022490895134375234945 1110766868171350781426209)
    ·
      refine ⟨833075151128513086069657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1110766868171350781426209 833075151128513086069657)
      ·
        refine ⟨624806363346384814552243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 833075151128513086069657 624806363346384814552243)
        ·
          refine ⟨937209545019577221828365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624806363346384814552243 937209545019577221828365)
          ·
            refine ⟨351453579382341458185637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 937209545019577221828365 351453579382341458185637)
            ·
              refine ⟨65897546134189023409807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 351453579382341458185637 65897546134189023409807)
              ·
                refine ⟨98846319201283535114711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65897546134189023409807 98846319201283535114711)
                ·
                  refine ⟨148269478801925302672067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98846319201283535114711 148269478801925302672067)
                  ·
                    refine ⟨222404218202887954008101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148269478801925302672067 222404218202887954008101)
                    ·
                      refine ⟨41700790913041491376519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 222404218202887954008101 41700790913041491376519)
                      ·
                        rfl

theorem cell23_81212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_81212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81212 prefixEnd_81212 := by exact prefixLift 81212
  have htrace : WordTrace (prefixWord ++ tailWord_81212) baseStart_81212 baseEnd_81212 := by
    simpa [prefixWord, tailWord_81212, baseEnd_81212] using wordTrace_append hprefix tailTrace_81212
  have hstable : (prefixWord ++ tailWord_81212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81212).length < 2 ^ (prefixWord ++ tailWord_81212).sum := by decide
  have hdescent : baseEnd_81212 < baseStart_81212 := by decide
  rcases family_descends (prefixWord ++ tailWord_81212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81335 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_81335 : Nat := 118140960795 + 81335 * 2 ^ 59
def prefixEnd_81335 : Nat := 4983230072969 + 3 ^ 40 * 81335 * 2
def baseEnd_81335 : Nat := 41763949033544510138453

theorem tailTrace_81335 : CollatzResearch.WordTrace tailWord_81335 prefixEnd_81335 41763949033544510138453 := by
  unfold tailWord_81335
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966531160344660757197459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1977687440229773838131639 2966531160344660757197459)
  ·
    refine ⟨4449796740516991135796189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2966531160344660757197459 4449796740516991135796189)
    ·
      refine ⟨1668673777693871675923571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4449796740516991135796189 1668673777693871675923571)
      ·
        refine ⟨2503010666540807513885357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668673777693871675923571 2503010666540807513885357)
        ·
          refine ⟨938628999952802817707009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2503010666540807513885357 938628999952802817707009)
          ·
            refine ⟨703971749964602113280257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 938628999952802817707009 703971749964602113280257)
            ·
              refine ⟨527978812473451584960193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703971749964602113280257 527978812473451584960193)
              ·
                refine ⟨395984109355088688720145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527978812473451584960193 395984109355088688720145)
                ·
                  refine ⟨296988082016316516540109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395984109355088688720145 296988082016316516540109)
                  ·
                    refine ⟨111370530756118693702541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296988082016316516540109 111370530756118693702541)
                    ·
                      refine ⟨41763949033544510138453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 111370530756118693702541 41763949033544510138453)
                      ·
                        rfl

theorem cell23_81335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_81335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81335 prefixEnd_81335 := by exact prefixLift 81335
  have htrace : WordTrace (prefixWord ++ tailWord_81335) baseStart_81335 baseEnd_81335 := by
    simpa [prefixWord, tailWord_81335, baseEnd_81335] using wordTrace_append hprefix tailTrace_81335
  have hstable : (prefixWord ++ tailWord_81335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81335).length < 2 ^ (prefixWord ++ tailWord_81335).sum := by decide
  have hdescent : baseEnd_81335 < baseStart_81335 := by decide
  rcases family_descends (prefixWord ++ tailWord_81335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81338 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_81338 : Nat := 118140960795 + 81338 * 2 ^ 59
def prefixEnd_81338 : Nat := 4983230072969 + 3 ^ 40 * 81338 * 2
def baseEnd_81338 : Nat := 13921829825169332800313

theorem tailTrace_81338 : CollatzResearch.WordTrace tailWord_81338 prefixEnd_81338 13921829825169332800313 := by
  unfold tailWord_81338
  simp only [CollatzResearch.WordTrace]
  refine ⟨741660144833448067389167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1977760386222528179704445 741660144833448067389167)
  ·
    refine ⟨1112490217250172101083751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741660144833448067389167 1112490217250172101083751)
    ·
      refine ⟨1668735325875258151625627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112490217250172101083751 1668735325875258151625627)
      ·
        refine ⟨2503102988812887227438441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668735325875258151625627 2503102988812887227438441)
        ·
          refine ⟨1877327241609665420578831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503102988812887227438441 1877327241609665420578831)
          ·
            refine ⟨2815990862414498130868247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877327241609665420578831 2815990862414498130868247)
            ·
              refine ⟨4223986293621747196302371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815990862414498130868247 4223986293621747196302371)
              ·
                refine ⟨6335979440432620794453557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4223986293621747196302371 6335979440432620794453557)
                ·
                  refine ⟨593998072540558199480021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6335979440432620794453557 593998072540558199480021)
                  ·
                    refine ⟨13921829825169332800313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 593998072540558199480021 13921829825169332800313)
                    ·
                      rfl

theorem cell23_81338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_81338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81338 prefixEnd_81338 := by exact prefixLift 81338
  have htrace : WordTrace (prefixWord ++ tailWord_81338) baseStart_81338 baseEnd_81338 := by
    simpa [prefixWord, tailWord_81338, baseEnd_81338] using wordTrace_append hprefix tailTrace_81338
  have hstable : (prefixWord ++ tailWord_81338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81338).length < 2 ^ (prefixWord ++ tailWord_81338).sum := by decide
  have hdescent : baseEnd_81338 < baseStart_81338 := by decide
  rcases family_descends (prefixWord ++ tailWord_81338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81375 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_81375 : Nat := 118140960795 + 81375 * 2 ^ 59
def prefixEnd_81375 : Nat := 4983230072969 + 3 ^ 40 * 81375 * 2
def baseEnd_81375 : Nat := 41784488259724353638269

theorem tailTrace_81375 : CollatzResearch.WordTrace tailWord_81375 prefixEnd_81375 41784488259724353638269 := by
  unfold tailWord_81375
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967990080199747588653579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1978660053466498392435719 2967990080199747588653579)
  ·
    refine ⟨4451985120299621382980369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2967990080199747588653579 4451985120299621382980369)
    ·
      refine ⟨3338988840224716037235277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4451985120299621382980369 3338988840224716037235277)
      ·
        refine ⟨1252120815084268513963229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3338988840224716037235277 1252120815084268513963229)
        ·
          refine ⟨469545305656600692736211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1252120815084268513963229 469545305656600692736211)
          ·
            refine ⟨704317958484901039104317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469545305656600692736211 704317958484901039104317)
            ·
              refine ⟨264119234431837889664119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 704317958484901039104317 264119234431837889664119)
              ·
                refine ⟨396178851647756834496179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264119234431837889664119 396178851647756834496179)
                ·
                  refine ⟨594268277471635251744269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396178851647756834496179 594268277471635251744269)
                  ·
                    refine ⟨222850604051863219404101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594268277471635251744269 222850604051863219404101)
                    ·
                      refine ⟨41784488259724353638269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 222850604051863219404101 41784488259724353638269)
                      ·
                        rfl

theorem cell23_81375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_81375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81375 prefixEnd_81375 := by exact prefixLift 81375
  have htrace : WordTrace (prefixWord ++ tailWord_81375) baseStart_81375 baseEnd_81375 := by
    simpa [prefixWord, tailWord_81375, baseEnd_81375] using wordTrace_append hprefix tailTrace_81375
  have hstable : (prefixWord ++ tailWord_81375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81375).length < 2 ^ (prefixWord ++ tailWord_81375).sum := by decide
  have hdescent : baseEnd_81375 < baseStart_81375 := by decide
  rcases family_descends (prefixWord ++ tailWord_81375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81392 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 2, 4, 2]
def baseStart_81392 : Nat := 118140960795 + 81392 * 2 ^ 59
def prefixEnd_81392 : Nat := 4983230072969 + 3 ^ 40 * 81392 * 2
def baseEnd_81392 : Nat := 41793217430850787125691

theorem tailTrace_81392 : CollatzResearch.WordTrace tailWord_81392 prefixEnd_81392 41793217430850787125691 := by
  unfold tailWord_81392
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484305060569079746011215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1979073414092106328014953 1484305060569079746011215)
  ·
    refine ⟨2226457590853619619016823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484305060569079746011215 2226457590853619619016823)
    ·
      refine ⟨3339686386280429428525235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2226457590853619619016823 3339686386280429428525235)
      ·
        refine ⟨5009529579420644142787853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339686386280429428525235 5009529579420644142787853)
        ·
          refine ⟨1878573592282741553545445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5009529579420644142787853 1878573592282741553545445)
          ·
            refine ⟨352232548553014041289771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1878573592282741553545445 352232548553014041289771)
            ·
              refine ⟨528348822829521061934657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352232548553014041289771 528348822829521061934657)
              ·
                refine ⟨396261617122140796450993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528348822829521061934657 396261617122140796450993)
                ·
                  refine ⟨297196212841605597338245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396261617122140796450993 297196212841605597338245)
                  ·
                    refine ⟨55724289907801049500921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297196212841605597338245 55724289907801049500921)
                    ·
                      refine ⟨41793217430850787125691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55724289907801049500921 41793217430850787125691)
                      ·
                        rfl

theorem cell23_81392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 4, 2].length) (baseStart_81392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81392 prefixEnd_81392 := by exact prefixLift 81392
  have htrace : WordTrace (prefixWord ++ tailWord_81392) baseStart_81392 baseEnd_81392 := by
    simpa [prefixWord, tailWord_81392, baseEnd_81392] using wordTrace_append hprefix tailTrace_81392
  have hstable : (prefixWord ++ tailWord_81392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81392).length < 2 ^ (prefixWord ++ tailWord_81392).sum := by decide
  have hdescent : baseEnd_81392 < baseStart_81392 := by decide
  rcases family_descends (prefixWord ++ tailWord_81392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81402 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_81402 : Nat := 118140960795 + 81402 * 2 ^ 59
def prefixEnd_81402 : Nat := 4983230072969 + 3 ^ 40 * 81402 * 2
def baseEnd_81402 : Nat := 13932784079131916000215

theorem tailTrace_81402 : CollatzResearch.WordTrace tailWord_81402 prefixEnd_81402 13932784079131916000215 := by
  unfold tailWord_81402
  simp only [CollatzResearch.WordTrace]
  refine ⟨742243712775482799971615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1979316567401287466590973 742243712775482799971615)
  ·
    refine ⟨1113365569163224199957423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742243712775482799971615 1113365569163224199957423)
    ·
      refine ⟨1670048353744836299936135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113365569163224199957423 1670048353744836299936135)
      ·
        refine ⟨2505072530617254449904203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670048353744836299936135 2505072530617254449904203)
        ·
          refine ⟨3757608795925881674856305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505072530617254449904203 3757608795925881674856305)
          ·
            refine ⟨2818206596944411256142229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3757608795925881674856305 2818206596944411256142229)
            ·
              refine ⟨132103434231769277631667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2818206596944411256142229 132103434231769277631667)
              ·
                refine ⟨198155151347653916447501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132103434231769277631667 198155151347653916447501)
                ·
                  refine ⟨74308181755370218667813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198155151347653916447501 74308181755370218667813)
                  ·
                    refine ⟨13932784079131916000215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74308181755370218667813 13932784079131916000215)
                    ·
                      rfl

theorem cell23_81402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_81402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81402 prefixEnd_81402 := by exact prefixLift 81402
  have htrace : WordTrace (prefixWord ++ tailWord_81402) baseStart_81402 baseEnd_81402 := by
    simpa [prefixWord, tailWord_81402, baseEnd_81402] using wordTrace_append hprefix tailTrace_81402
  have hstable : (prefixWord ++ tailWord_81402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81402).length < 2 ^ (prefixWord ++ tailWord_81402).sum := by decide
  have hdescent : baseEnd_81402 < baseStart_81402 := by decide
  rcases family_descends (prefixWord ++ tailWord_81402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81425 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_81425 : Nat := 118140960795 + 81425 * 2 ^ 59
def prefixEnd_81425 : Nat := 4983230072969 + 3 ^ 40 * 81425 * 2
def baseEnd_81425 : Nat := 41810162292449158013039

theorem tailTrace_81425 : CollatzResearch.WordTrace tailWord_81425 prefixEnd_81425 41810162292449158013039 := by
  unfold tailWord_81425
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969813730018606127973729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1979875820012404085315819 2969813730018606127973729)
  ·
    refine ⟨2227360297513954595980297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2969813730018606127973729 2227360297513954595980297)
    ·
      refine ⟨1670520223135465946985223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2227360297513954595980297 1670520223135465946985223)
      ·
        refine ⟨2505780334703198920477835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670520223135465946985223 2505780334703198920477835)
        ·
          refine ⟨3758670502054798380716753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505780334703198920477835 3758670502054798380716753)
          ·
            refine ⟨2819002876541098785537565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758670502054798380716753 2819002876541098785537565)
            ·
              refine ⟨1057126078702912044576587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2819002876541098785537565 1057126078702912044576587)
              ·
                refine ⟨1585689118054368066864881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057126078702912044576587 1585689118054368066864881)
                ·
                  refine ⟨1189266838540776050148661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1585689118054368066864881 1189266838540776050148661)
                  ·
                    refine ⟨111493766113197754701437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1189266838540776050148661 111493766113197754701437)
                    ·
                      refine ⟨41810162292449158013039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 111493766113197754701437 41810162292449158013039)
                      ·
                        rfl

theorem cell23_81425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_81425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81425 prefixEnd_81425 := by exact prefixLift 81425
  have htrace : WordTrace (prefixWord ++ tailWord_81425) baseStart_81425 baseEnd_81425 := by
    simpa [prefixWord, tailWord_81425, baseEnd_81425] using wordTrace_append hprefix tailTrace_81425
  have hstable : (prefixWord ++ tailWord_81425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81425).length < 2 ^ (prefixWord ++ tailWord_81425).sum := by decide
  have hdescent : baseEnd_81425 < baseStart_81425 := by decide
  rcases family_descends (prefixWord ++ tailWord_81425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81445 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_81445 : Nat := 118140960795 + 81445 * 2 ^ 59
def prefixEnd_81445 : Nat := 4983230072969 + 3 ^ 40 * 81445 * 2
def baseEnd_81445 : Nat := 13940143968513026587649

theorem tailTrace_81445 : CollatzResearch.WordTrace tailWord_81445 prefixEnd_81445 13940143968513026587649 := by
  unfold tailWord_81445
  simp only [CollatzResearch.WordTrace]
  refine ⟨2970543189946149543701789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1980362126630766362467859 2970543189946149543701789)
  ·
    refine ⟨1113953696229806078888171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2970543189946149543701789 1113953696229806078888171)
    ·
      refine ⟨1670930544344709118332257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113953696229806078888171 1670930544344709118332257)
      ·
        refine ⟨1253197908258531838749193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1670930544344709118332257 1253197908258531838749193)
        ·
          refine ⟨939898431193898879061895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253197908258531838749193 939898431193898879061895)
          ·
            refine ⟨1409847646790848318592843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939898431193898879061895 1409847646790848318592843)
            ·
              refine ⟨2114771470186272477889265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409847646790848318592843 2114771470186272477889265)
              ·
                refine ⟨1586078602639704358416949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114771470186272477889265 1586078602639704358416949)
                ·
                  refine ⟨148694868997472283601589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586078602639704358416949 148694868997472283601589)
                  ·
                    refine ⟨13940143968513026587649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148694868997472283601589 13940143968513026587649)
                    ·
                      rfl

theorem cell23_81445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_81445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81445 prefixEnd_81445 := by exact prefixLift 81445
  have htrace : WordTrace (prefixWord ++ tailWord_81445) baseStart_81445 baseEnd_81445 := by
    simpa [prefixWord, tailWord_81445, baseEnd_81445] using wordTrace_append hprefix tailTrace_81445
  have hstable : (prefixWord ++ tailWord_81445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81445).length < 2 ^ (prefixWord ++ tailWord_81445).sum := by decide
  have hdescent : baseEnd_81445 < baseStart_81445 := by decide
  rcases family_descends (prefixWord ++ tailWord_81445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81459 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 3]
def baseStart_81459 : Nat := 118140960795 + 81459 * 2 ^ 59
def prefixEnd_81459 : Nat := 4983230072969 + 3 ^ 40 * 81459 * 2
def baseEnd_81459 : Nat := 41827620634702024987883

theorem tailTrace_81459 : CollatzResearch.WordTrace tailWord_81459 prefixEnd_81459 41827620634702024987883 := by
  unfold tailWord_81459
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971053811895429934711431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1980702541263619956474287 2971053811895429934711431)
  ·
    refine ⟨4456580717843144902067147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2971053811895429934711431 4456580717843144902067147)
    ·
      refine ⟨6684871076764717353100721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456580717843144902067147 6684871076764717353100721)
      ·
        refine ⟨5013653307573538014825541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6684871076764717353100721 5013653307573538014825541)
        ·
          refine ⟨940059995170038377779789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5013653307573538014825541 940059995170038377779789)
          ·
            refine ⟨352522498188764391667421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 940059995170038377779789 352522498188764391667421)
            ·
              refine ⟨132195936820786646875283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352522498188764391667421 132195936820786646875283)
              ·
                refine ⟨198293905231179970312925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132195936820786646875283 198293905231179970312925)
                ·
                  refine ⟨74360214461692488867347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198293905231179970312925 74360214461692488867347)
                  ·
                    refine ⟨111540321692538733301021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74360214461692488867347 111540321692538733301021)
                    ·
                      refine ⟨41827620634702024987883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 111540321692538733301021 41827620634702024987883)
                      ·
                        rfl

theorem cell23_81459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_81459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81459 prefixEnd_81459 := by exact prefixLift 81459
  have htrace : WordTrace (prefixWord ++ tailWord_81459) baseStart_81459 baseEnd_81459 := by
    simpa [prefixWord, tailWord_81459, baseEnd_81459] using wordTrace_append hprefix tailTrace_81459
  have hstable : (prefixWord ++ tailWord_81459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81459).length < 2 ^ (prefixWord ++ tailWord_81459).sum := by decide
  have hdescent : baseEnd_81459 < baseStart_81459 := by decide
  rcases family_descends (prefixWord ++ tailWord_81459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81482 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_81482 : Nat := 118140960795 + 81482 * 2 ^ 59
def prefixEnd_81482 : Nat := 4983230072969 + 3 ^ 40 * 81482 * 2
def baseEnd_81482 : Nat := 41839430689755435000277

theorem tailTrace_81482 : CollatzResearch.WordTrace tailWord_81482 prefixEnd_81482 41839430689755435000277 := by
  unfold tailWord_81482
  simp only [CollatzResearch.WordTrace]
  refine ⟨742973172703026215699675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1981261793874736575199133 742973172703026215699675)
  ·
    refine ⟨1114459759054539323549513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742973172703026215699675 1114459759054539323549513)
    ·
      refine ⟨835844819290904492662135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1114459759054539323549513 835844819290904492662135)
      ·
        refine ⟨1253767228936356738993203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835844819290904492662135 1253767228936356738993203)
        ·
          refine ⟨1880650843404535108489805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253767228936356738993203 1880650843404535108489805)
          ·
            refine ⟨705244066276700665683677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1880650843404535108489805 705244066276700665683677)
            ·
              refine ⟨264466524853762749631379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705244066276700665683677 264466524853762749631379)
              ·
                refine ⟨396699787280644124447069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264466524853762749631379 396699787280644124447069)
                ·
                  refine ⟨148762420230241546667651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396699787280644124447069 148762420230241546667651)
                  ·
                    refine ⟨223143630345362320001477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148762420230241546667651 223143630345362320001477)
                    ·
                      refine ⟨41839430689755435000277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 223143630345362320001477 41839430689755435000277)
                      ·
                        rfl

theorem cell23_81482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_81482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81482 prefixEnd_81482 := by exact prefixLift 81482
  have htrace : WordTrace (prefixWord ++ tailWord_81482) baseStart_81482 baseEnd_81482 := by
    simpa [prefixWord, tailWord_81482, baseEnd_81482] using wordTrace_append hprefix tailTrace_81482
  have hstable : (prefixWord ++ tailWord_81482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81482).length < 2 ^ (prefixWord ++ tailWord_81482).sum := by decide
  have hdescent : baseEnd_81482 < baseStart_81482 := by decide
  rcases family_descends (prefixWord ++ tailWord_81482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81492 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_81492 : Nat := 118140960795 + 81492 * 2 ^ 59
def prefixEnd_81492 : Nat := 4983230072969 + 3 ^ 40 * 81492 * 2
def baseEnd_81492 : Nat := 13948188498766798625077

theorem tailTrace_81492 : CollatzResearch.WordTrace tailWord_81492 prefixEnd_81492 13948188498766798625077 := by
  unfold tailWord_81492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486128710387938285331365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1981504947183917713775153 1486128710387938285331365)
  ·
    refine ⟨278649133197738428499631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1486128710387938285331365 278649133197738428499631)
    ·
      refine ⟨417973699796607642749447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278649133197738428499631 417973699796607642749447)
      ·
        refine ⟨626960549694911464124171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417973699796607642749447 626960549694911464124171)
        ·
          refine ⟨940440824542367196186257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626960549694911464124171 940440824542367196186257)
          ·
            refine ⟨705330618406775397139693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940440824542367196186257 705330618406775397139693)
            ·
              refine ⟨264498981902540773927385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705330618406775397139693 264498981902540773927385)
              ·
                refine ⟨198374236426905580445539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264498981902540773927385 198374236426905580445539)
                ·
                  refine ⟨297561354640358370668309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198374236426905580445539 297561354640358370668309)
                  ·
                    refine ⟨13948188498766798625077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 297561354640358370668309 13948188498766798625077)
                    ·
                      rfl

theorem cell23_81492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_81492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81492 prefixEnd_81492 := by exact prefixLift 81492
  have htrace : WordTrace (prefixWord ++ tailWord_81492) baseStart_81492 baseEnd_81492 := by
    simpa [prefixWord, tailWord_81492, baseEnd_81492] using wordTrace_append hprefix tailTrace_81492
  have hstable : (prefixWord ++ tailWord_81492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81492).length < 2 ^ (prefixWord ++ tailWord_81492).sum := by decide
  have hdescent : baseEnd_81492 < baseStart_81492 := by decide
  rcases family_descends (prefixWord ++ tailWord_81492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81509 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_81509 : Nat := 118140960795 + 81509 * 2 ^ 59
def prefixEnd_81509 : Nat := 4983230072969 + 3 ^ 40 * 81509 * 2
def baseEnd_81509 : Nat := 13951098222475609787551

theorem tailTrace_81509 : CollatzResearch.WordTrace tailWord_81509 prefixEnd_81509 13951098222475609787551 := by
  unfold tailWord_81509
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972877461714288474031581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1981918307809525649354387 2972877461714288474031581)
  ·
    refine ⟨1114829048142858177761843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2972877461714288474031581 1114829048142858177761843)
    ·
      refine ⟨1672243572214287266642765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114829048142858177761843 1672243572214287266642765)
      ·
        refine ⟨627091339580357724991037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1672243572214287266642765 627091339580357724991037)
        ·
          refine ⟨235159252342634146871639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627091339580357724991037 235159252342634146871639)
          ·
            refine ⟨352738878513951220307459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235159252342634146871639 352738878513951220307459)
            ·
              refine ⟨529108317770926830461189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352738878513951220307459 529108317770926830461189)
              ·
                refine ⟨99207809582048780711473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529108317770926830461189 99207809582048780711473)
                ·
                  refine ⟨74405857186536585533605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99207809582048780711473 74405857186536585533605)
                  ·
                    refine ⟨13951098222475609787551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74405857186536585533605 13951098222475609787551)
                    ·
                      rfl

theorem cell23_81509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_81509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81509 prefixEnd_81509 := by exact prefixLift 81509
  have htrace : WordTrace (prefixWord ++ tailWord_81509) baseStart_81509 baseEnd_81509 := by
    simpa [prefixWord, tailWord_81509, baseEnd_81509] using wordTrace_append hprefix tailTrace_81509
  have hstable : (prefixWord ++ tailWord_81509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81509).length < 2 ^ (prefixWord ++ tailWord_81509).sum := by decide
  have hdescent : baseEnd_81509 < baseStart_81509 := by decide
  rcases family_descends (prefixWord ++ tailWord_81509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81522 : List Nat := [3, 2, 1, 2, 3, 1, 3, 8]
def baseStart_81522 : Nat := 118140960795 + 81522 * 2 ^ 59
def prefixEnd_81522 : Nat := 4983230072969 + 3 ^ 40 * 81522 * 2
def baseEnd_81522 : Nat := 1550369256145751055559

theorem tailTrace_81522 : CollatzResearch.WordTrace tailWord_81522 prefixEnd_81522 1550369256145751055559 := by
  unfold tailWord_81522
  simp only [CollatzResearch.WordTrace]
  refine ⟨743337902666797923563705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1982234407111461129503213 743337902666797923563705)
  ·
    refine ⟨557503427000098442672779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 743337902666797923563705 557503427000098442672779)
    ·
      refine ⟨836255140500147664009169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557503427000098442672779 836255140500147664009169)
      ·
        refine ⟨627191355375110748006877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 836255140500147664009169 627191355375110748006877)
        ·
          refine ⟨235196758265666530502579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627191355375110748006877 235196758265666530502579)
          ·
            refine ⟨352795137398499795753869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235196758265666530502579 352795137398499795753869)
            ·
              refine ⟨132298176524437423407701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352795137398499795753869 132298176524437423407701)
              ·
                refine ⟨1550369256145751055559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 132298176524437423407701 1550369256145751055559)
                ·
                  rfl

theorem cell23_81522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_81522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81522 prefixEnd_81522 := by exact prefixLift 81522
  have htrace : WordTrace (prefixWord ++ tailWord_81522) baseStart_81522 baseEnd_81522 := by
    simpa [prefixWord, tailWord_81522, baseEnd_81522] using wordTrace_append hprefix tailTrace_81522
  have hstable : (prefixWord ++ tailWord_81522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81522).length < 2 ^ (prefixWord ++ tailWord_81522).sum := by decide
  have hdescent : baseEnd_81522 < baseStart_81522 := by decide
  rcases family_descends (prefixWord ++ tailWord_81522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81526 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_81526 : Nat := 118140960795 + 81526 * 2 ^ 59
def prefixEnd_81526 : Nat := 4983230072969 + 3 ^ 40 * 81526 * 2
def baseEnd_81526 : Nat := 13954007946184420950025

theorem tailTrace_81526 : CollatzResearch.WordTrace tailWord_81526 prefixEnd_81526 13954007946184420950025 := by
  unfold tailWord_81526
  simp only [CollatzResearch.WordTrace]
  refine ⟨185843593915793773587527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1982331668435133584933621 185843593915793773587527)
  ·
    refine ⟨278765390873690660381291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185843593915793773587527 278765390873690660381291)
    ·
      refine ⟨418148086310535990571937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278765390873690660381291 418148086310535990571937)
      ·
        refine ⟨313611064732901992928953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418148086310535990571937 313611064732901992928953)
        ·
          refine ⟨235208298549676494696715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313611064732901992928953 235208298549676494696715)
          ·
            refine ⟨352812447824514742045073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235208298549676494696715 352812447824514742045073)
            ·
              refine ⟨264609335868386056533805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352812447824514742045073 264609335868386056533805)
              ·
                refine ⟨99228500950644771200177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264609335868386056533805 99228500950644771200177)
                ·
                  refine ⟨74421375712983578400133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99228500950644771200177 74421375712983578400133)
                  ·
                    refine ⟨13954007946184420950025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74421375712983578400133 13954007946184420950025)
                    ·
                      rfl

theorem cell23_81526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_81526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81526 prefixEnd_81526 := by exact prefixLift 81526
  have htrace : WordTrace (prefixWord ++ tailWord_81526) baseStart_81526 baseEnd_81526 := by
    simpa [prefixWord, tailWord_81526, baseEnd_81526] using wordTrace_append hprefix tailTrace_81526
  have hstable : (prefixWord ++ tailWord_81526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81526).length < 2 ^ (prefixWord ++ tailWord_81526).sum := by decide
  have hdescent : baseEnd_81526 < baseStart_81526 := by decide
  rcases family_descends (prefixWord ++ tailWord_81526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81550 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_81550 : Nat := 118140960795 + 81550 * 2 ^ 59
def prefixEnd_81550 : Nat := 4983230072969 + 3 ^ 40 * 81550 * 2
def baseEnd_81550 : Nat := 41874347374261168949965

theorem tailTrace_81550 : CollatzResearch.WordTrace tailWord_81550 prefixEnd_81550 41874347374261168949965 := by
  unfold tailWord_81550
  simp only [CollatzResearch.WordTrace]
  refine ⟨371796606820719059534263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1982915236377168317516069 371796606820719059534263)
  ·
    refine ⟨557694910231078589301395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371796606820719059534263 557694910231078589301395)
    ·
      refine ⟨836542365346617883952093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557694910231078589301395 836542365346617883952093)
      ·
        refine ⟨313703387004981706482035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 836542365346617883952093 313703387004981706482035)
        ·
          refine ⟨470555080507472559723053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313703387004981706482035 470555080507472559723053)
          ·
            refine ⟨176458155190302209896145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470555080507472559723053 176458155190302209896145)
            ·
              refine ⟨132343616392726657422109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176458155190302209896145 132343616392726657422109)
              ·
                refine ⟨49628856147272496533291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132343616392726657422109 49628856147272496533291)
                ·
                  refine ⟨74443284220908744799937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49628856147272496533291 74443284220908744799937)
                  ·
                    refine ⟨55832463165681558599953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74443284220908744799937 55832463165681558599953)
                    ·
                      refine ⟨41874347374261168949965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55832463165681558599953 41874347374261168949965)
                      ·
                        rfl

theorem cell23_81550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_81550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81550 prefixEnd_81550 := by exact prefixLift 81550
  have htrace : WordTrace (prefixWord ++ tailWord_81550) baseStart_81550 baseEnd_81550 := by
    simpa [prefixWord, tailWord_81550, baseEnd_81550] using wordTrace_append hprefix tailTrace_81550
  have hstable : (prefixWord ++ tailWord_81550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81550).length < 2 ^ (prefixWord ++ tailWord_81550).sum := by decide
  have hdescent : baseEnd_81550 < baseStart_81550 := by decide
  rcases family_descends (prefixWord ++ tailWord_81550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81592 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_81592 : Nat := 118140960795 + 81592 * 2 ^ 59
def prefixEnd_81592 : Nat := 4983230072969 + 3 ^ 40 * 81592 * 2
def baseEnd_81592 : Nat := 41895913561750004624771

theorem tailTrace_81592 : CollatzResearch.WordTrace tailWord_81592 prefixEnd_81592 41895913561750004624771 := by
  unfold tailWord_81592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487952360206796824651515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1983936480275729099535353 1487952360206796824651515)
  ·
    refine ⟨2231928540310195236977273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487952360206796824651515 2231928540310195236977273)
    ·
      refine ⟨1673946405232646427732955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2231928540310195236977273 1673946405232646427732955)
      ·
        refine ⟨2510919607848969641599433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673946405232646427732955 2510919607848969641599433)
        ·
          refine ⟨1883189705886727231199575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2510919607848969641599433 1883189705886727231199575)
          ·
            refine ⟨2824784558830090846799363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883189705886727231199575 2824784558830090846799363)
            ·
              refine ⟨4237176838245136270199045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824784558830090846799363 4237176838245136270199045)
              ·
                refine ⟨794470657170963050662321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4237176838245136270199045 794470657170963050662321)
                ·
                  refine ⟨595852992878222287996741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 794470657170963050662321 595852992878222287996741)
                  ·
                    refine ⟨111722436164666678999389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595852992878222287996741 111722436164666678999389)
                    ·
                      refine ⟨41895913561750004624771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 111722436164666678999389 41895913561750004624771)
                      ·
                        rfl

theorem cell23_81592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_81592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81592 prefixEnd_81592 := by exact prefixLift 81592
  have htrace : WordTrace (prefixWord ++ tailWord_81592) baseStart_81592 baseEnd_81592 := by
    simpa [prefixWord, tailWord_81592, baseEnd_81592] using wordTrace_append hprefix tailTrace_81592
  have hstable : (prefixWord ++ tailWord_81592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81592).length < 2 ^ (prefixWord ++ tailWord_81592).sum := by decide
  have hdescent : baseEnd_81592 < baseStart_81592 := by decide
  rcases family_descends (prefixWord ++ tailWord_81592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81640 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_81640 : Nat := 118140960795 + 81640 * 2 ^ 59
def prefixEnd_81640 : Nat := 4983230072969 + 3 ^ 40 * 81640 * 2
def baseEnd_81640 : Nat := 41920560633165816824551

theorem tailTrace_81640 : CollatzResearch.WordTrace tailWord_81640 prefixEnd_81640 41920560633165816824551 := by
  unfold tailWord_81640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488827712119848923525187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1985103616159798564700249 1488827712119848923525187)
  ·
    refine ⟨2233241568179773385287781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1488827712119848923525187 2233241568179773385287781)
    ·
      refine ⟨418732794033707509741459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2233241568179773385287781 418732794033707509741459)
      ·
        refine ⟨628099191050561264612189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418732794033707509741459 628099191050561264612189)
        ·
          refine ⟨235537196643960474229571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 628099191050561264612189 235537196643960474229571)
          ·
            refine ⟨353305794965940711344357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235537196643960474229571 353305794965940711344357)
            ·
              refine ⟨66244836556113883377067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 353305794965940711344357 66244836556113883377067)
              ·
                refine ⟨99367254834170825065601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66244836556113883377067 99367254834170825065601)
                ·
                  refine ⟨74525441125628118799201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99367254834170825065601 74525441125628118799201)
                  ·
                    refine ⟨55894080844221089099401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74525441125628118799201 55894080844221089099401)
                    ·
                      refine ⟨41920560633165816824551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55894080844221089099401 41920560633165816824551)
                      ·
                        rfl

theorem cell23_81640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_81640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81640 prefixEnd_81640 := by exact prefixLift 81640
  have htrace : WordTrace (prefixWord ++ tailWord_81640) baseStart_81640 baseEnd_81640 := by
    simpa [prefixWord, tailWord_81640, baseEnd_81640] using wordTrace_append hprefix tailTrace_81640
  have hstable : (prefixWord ++ tailWord_81640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81640).length < 2 ^ (prefixWord ++ tailWord_81640).sum := by decide
  have hdescent : baseEnd_81640 < baseStart_81640 := by decide
  rcases family_descends (prefixWord ++ tailWord_81640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81642 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_81642 : Nat := 118140960795 + 81642 * 2 ^ 59
def prefixEnd_81642 : Nat := 4983230072969 + 3 ^ 40 * 81642 * 2
def baseEnd_81642 : Nat := 13973862531491602999847

theorem tailTrace_81642 : CollatzResearch.WordTrace tailWord_81642 prefixEnd_81642 13973862531491602999847 := by
  unfold tailWord_81642
  simp only [CollatzResearch.WordTrace]
  refine ⟨744432092558113047155795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1985152246821634792415453 744432092558113047155795)
  ·
    refine ⟨1116648138837169570733693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744432092558113047155795 1116648138837169570733693)
    ·
      refine ⟨418743052063938589025135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1116648138837169570733693 418743052063938589025135)
      ·
        refine ⟨628114578095907883537703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418743052063938589025135 628114578095907883537703)
        ·
          refine ⟨942171867143861825306555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628114578095907883537703 942171867143861825306555)
          ·
            refine ⟨1413257800715792737959833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942171867143861825306555 1413257800715792737959833)
            ·
              refine ⟨1059943350536844553469875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1413257800715792737959833 1059943350536844553469875)
              ·
                refine ⟨1589915025805266830204813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059943350536844553469875 1589915025805266830204813)
                ·
                  refine ⟨596218134676975061326805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1589915025805266830204813 596218134676975061326805)
                  ·
                    refine ⟨13973862531491602999847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 596218134676975061326805 13973862531491602999847)
                    ·
                      rfl

theorem cell23_81642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_81642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81642 prefixEnd_81642 := by exact prefixLift 81642
  have htrace : WordTrace (prefixWord ++ tailWord_81642) baseStart_81642 baseEnd_81642 := by
    simpa [prefixWord, tailWord_81642, baseEnd_81642] using wordTrace_append hprefix tailTrace_81642
  have hstable : (prefixWord ++ tailWord_81642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81642).length < 2 ^ (prefixWord ++ tailWord_81642).sum := by decide
  have hdescent : baseEnd_81642 < baseStart_81642 := by decide
  rcases family_descends (prefixWord ++ tailWord_81642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81696 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 2, 4, 2]
def baseStart_81696 : Nat := 118140960795 + 81696 * 2 ^ 59
def prefixEnd_81696 : Nat := 4983230072969 + 3 ^ 40 * 81696 * 2
def baseEnd_81696 : Nat := 41949315549817597724293

theorem tailTrace_81696 : CollatzResearch.WordTrace tailWord_81696 prefixEnd_81696 41949315549817597724293 := by
  unfold tailWord_81696
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489848956018409705544471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1986465274691212940725961 1489848956018409705544471)
  ·
    refine ⟨2234773434027614558316707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1489848956018409705544471 2234773434027614558316707)
    ·
      refine ⟨3352160151041421837475061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234773434027614558316707 3352160151041421837475061)
      ·
        refine ⟨314265014160133297263287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3352160151041421837475061 314265014160133297263287)
        ·
          refine ⟨471397521240199945894931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314265014160133297263287 471397521240199945894931)
          ·
            refine ⟨707096281860299918842397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471397521240199945894931 707096281860299918842397)
            ·
              refine ⟨265161105697612469565899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 707096281860299918842397 265161105697612469565899)
              ·
                refine ⟨397741658546418704348849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265161105697612469565899 397741658546418704348849)
                ·
                  refine ⟨298306243909814028261637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397741658546418704348849 298306243909814028261637)
                  ·
                    refine ⟨55932420733090130299057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298306243909814028261637 55932420733090130299057)
                    ·
                      refine ⟨41949315549817597724293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55932420733090130299057 41949315549817597724293)
                      ·
                        rfl

theorem cell23_81696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_81696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81696 prefixEnd_81696 := by exact prefixLift 81696
  have htrace : WordTrace (prefixWord ++ tailWord_81696) baseStart_81696 baseEnd_81696 := by
    simpa [prefixWord, tailWord_81696, baseEnd_81696] using wordTrace_append hprefix tailTrace_81696
  have hstable : (prefixWord ++ tailWord_81696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81696).length < 2 ^ (prefixWord ++ tailWord_81696).sum := by decide
  have hdescent : baseEnd_81696 < baseStart_81696 := by decide
  rcases family_descends (prefixWord ++ tailWord_81696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81699 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 3]
def baseStart_81699 : Nat := 118140960795 + 81699 * 2 ^ 59
def prefixEnd_81699 : Nat := 4983230072969 + 3 ^ 40 * 81699 * 2
def baseEnd_81699 : Nat := 41950855991781085986779

theorem tailTrace_81699 : CollatzResearch.WordTrace tailWord_81699 prefixEnd_81699 41950855991781085986779 := by
  unfold tailWord_81699
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979807331025950923448151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1986538220683967282298767 2979807331025950923448151)
  ·
    refine ⟨4469710996538926385172227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2979807331025950923448151 4469710996538926385172227)
    ·
      refine ⟨6704566494808389577758341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469710996538926385172227 6704566494808389577758341)
      ·
        refine ⟨1257106217776573045829689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6704566494808389577758341 1257106217776573045829689)
        ·
          refine ⟨942829663332429784372267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257106217776573045829689 942829663332429784372267)
          ·
            refine ⟨1414244494998644676558401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942829663332429784372267 1414244494998644676558401)
            ·
              refine ⟨1060683371248983507418801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414244494998644676558401 1060683371248983507418801)
              ·
                refine ⟨795512528436737630564101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060683371248983507418801 795512528436737630564101)
                ·
                  refine ⟨149158599081888305730769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795512528436737630564101 149158599081888305730769)
                  ·
                    refine ⟨111868949311416229298077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149158599081888305730769 111868949311416229298077)
                    ·
                      refine ⟨41950855991781085986779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 111868949311416229298077 41950855991781085986779)
                      ·
                        rfl

theorem cell23_81699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_81699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81699 prefixEnd_81699 := by exact prefixLift 81699
  have htrace : WordTrace (prefixWord ++ tailWord_81699) baseStart_81699 baseEnd_81699 := by
    simpa [prefixWord, tailWord_81699, baseEnd_81699] using wordTrace_append hprefix tailTrace_81699
  have hstable : (prefixWord ++ tailWord_81699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81699).length < 2 ^ (prefixWord ++ tailWord_81699).sum := by decide
  have hdescent : baseEnd_81699 < baseStart_81699 := by decide
  rcases family_descends (prefixWord ++ tailWord_81699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81710 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_81710 : Nat := 118140960795 + 81710 * 2 ^ 59
def prefixEnd_81710 : Nat := 4983230072969 + 3 ^ 40 * 81710 * 2
def baseEnd_81710 : Nat := 13985501426326847649743

theorem tailTrace_81710 : CollatzResearch.WordTrace tailWord_81710 prefixEnd_81710 13985501426326847649743 := by
  unfold tailWord_81710
  simp only [CollatzResearch.WordTrace]
  refine ⟨372526066748262475262323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1986805689324066534732389 372526066748262475262323)
  ·
    refine ⟨558789100122393712893485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 372526066748262475262323 558789100122393712893485)
    ·
      refine ⟨209545912545897642335057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 558789100122393712893485 209545912545897642335057)
      ·
        refine ⟨157159434409423231751293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209545912545897642335057 157159434409423231751293)
        ·
          refine ⟨58934787903533711906735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157159434409423231751293 58934787903533711906735)
          ·
            refine ⟨88402181855300567860103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58934787903533711906735 88402181855300567860103)
            ·
              refine ⟨132603272782950851790155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88402181855300567860103 132603272782950851790155)
              ·
                refine ⟨198904909174426277685233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132603272782950851790155 198904909174426277685233)
                ·
                  refine ⟨149178681880819708263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198904909174426277685233 149178681880819708263925)
                  ·
                    refine ⟨13985501426326847649743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149178681880819708263925 13985501426326847649743)
                    ·
                      rfl

theorem cell23_81710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_81710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81710 prefixEnd_81710 := by exact prefixLift 81710
  have htrace : WordTrace (prefixWord ++ tailWord_81710) baseStart_81710 baseEnd_81710 := by
    simpa [prefixWord, tailWord_81710, baseEnd_81710] using wordTrace_append hprefix tailTrace_81710
  have hstable : (prefixWord ++ tailWord_81710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81710).length < 2 ^ (prefixWord ++ tailWord_81710).sum := by decide
  have hdescent : baseEnd_81710 < baseStart_81710 := by decide
  rcases family_descends (prefixWord ++ tailWord_81710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81736 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 6]
def baseStart_81736 : Nat := 118140960795 + 81736 * 2 ^ 59
def prefixEnd_81736 : Nat := 4983230072969 + 3 ^ 40 * 81736 * 2
def baseEnd_81736 : Nat := 4663317197333049024901

theorem tailTrace_81736 : CollatzResearch.WordTrace tailWord_81736 prefixEnd_81736 4663317197333049024901 := by
  unfold tailWord_81736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490578415945953121272531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1987437887927937495030041 1490578415945953121272531)
  ·
    refine ⟨2235867623918929681908797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490578415945953121272531 2235867623918929681908797)
    ·
      refine ⟨838450358969598630715799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2235867623918929681908797 838450358969598630715799)
      ·
        refine ⟨1257675538454397946073699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838450358969598630715799 1257675538454397946073699)
        ·
          refine ⟨1886513307681596919110549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257675538454397946073699 1886513307681596919110549)
          ·
            refine ⟨88430311297574855583307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1886513307681596919110549 88430311297574855583307)
            ·
              refine ⟨132645466946362283374961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88430311297574855583307 132645466946362283374961)
              ·
                refine ⟨99484100209771712531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132645466946362283374961 99484100209771712531221)
                ·
                  refine ⟨4663317197333049024901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99484100209771712531221 4663317197333049024901)
                  ·
                    rfl

theorem cell23_81736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 6].length) (baseStart_81736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81736 prefixEnd_81736 := by exact prefixLift 81736
  have htrace : WordTrace (prefixWord ++ tailWord_81736) baseStart_81736 baseEnd_81736 := by
    simpa [prefixWord, tailWord_81736, baseEnd_81736] using wordTrace_append hprefix tailTrace_81736
  have hstable : (prefixWord ++ tailWord_81736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81736).length < 2 ^ (prefixWord ++ tailWord_81736).sum := by decide
  have hdescent : baseEnd_81736 < baseStart_81736 := by decide
  rcases family_descends (prefixWord ++ tailWord_81736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81769 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_81769 : Nat := 118140960795 + 81769 * 2 ^ 59
def prefixEnd_81769 : Nat := 4983230072969 + 3 ^ 40 * 81769 * 2
def baseEnd_81769 : Nat := 41986799637595812111457

theorem tailTrace_81769 : CollatzResearch.WordTrace tailWord_81769 prefixEnd_81769 41986799637595812111457 := by
  unfold tailWord_81769
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982360440772352878496361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1988240293848235252330907 2982360440772352878496361)
  ·
    refine ⟨2236770330579264658872271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2982360440772352878496361 2236770330579264658872271)
    ·
      refine ⟨3355155495868896988308407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236770330579264658872271 3355155495868896988308407)
      ·
        refine ⟨5032733243803345482462611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355155495868896988308407 5032733243803345482462611)
        ·
          refine ⟨7549099865705018223693917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032733243803345482462611 7549099865705018223693917)
          ·
            refine ⟨2830912449639381833885219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7549099865705018223693917 2830912449639381833885219)
            ·
              refine ⟨4246368674459072750827829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830912449639381833885219 4246368674459072750827829)
              ·
                refine ⟨398097063230538070390109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4246368674459072750827829 398097063230538070390109)
                ·
                  refine ⟨149286398711451776396291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398097063230538070390109 149286398711451776396291)
                  ·
                    refine ⟨223929598067177664594437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149286398711451776396291 223929598067177664594437)
                    ·
                      refine ⟨41986799637595812111457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 223929598067177664594437 41986799637595812111457)
                      ·
                        rfl

theorem cell23_81769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_81769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81769 prefixEnd_81769 := by exact prefixLift 81769
  have htrace : WordTrace (prefixWord ++ tailWord_81769) baseStart_81769 baseEnd_81769 := by
    simpa [prefixWord, tailWord_81769, baseEnd_81769] using wordTrace_append hprefix tailTrace_81769
  have hstable : (prefixWord ++ tailWord_81769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81769).length < 2 ^ (prefixWord ++ tailWord_81769).sum := by decide
  have hdescent : baseEnd_81769 < baseStart_81769 := by decide
  rcases family_descends (prefixWord ++ tailWord_81769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81786 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_81786 : Nat := 118140960795 + 81786 * 2 ^ 59
def prefixEnd_81786 : Nat := 4983230072969 + 3 ^ 40 * 81786 * 2
def baseEnd_81786 : Nat := 41995528808722245598879

theorem tailTrace_81786 : CollatzResearch.WordTrace tailWord_81786 prefixEnd_81786 41995528808722245598879 := by
  unfold tailWord_81786
  simp only [CollatzResearch.WordTrace]
  refine ⟨745745120427691195466303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1988653654473843187910141 745745120427691195466303)
  ·
    refine ⟨1118617680641536793199455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745745120427691195466303 1118617680641536793199455)
    ·
      refine ⟨1677926520962305189799183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118617680641536793199455 1677926520962305189799183)
      ·
        refine ⟨2516889781443457784698775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677926520962305189799183 2516889781443457784698775)
        ·
          refine ⟨3775334672165186677048163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516889781443457784698775 3775334672165186677048163)
          ·
            refine ⟨5663002008247780015572245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775334672165186677048163 5663002008247780015572245)
            ·
              refine ⟨265453219136614688229949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5663002008247780015572245 265453219136614688229949)
              ·
                refine ⟨99544957176230508086231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265453219136614688229949 99544957176230508086231)
                ·
                  refine ⟨149317435764345762129347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99544957176230508086231 149317435764345762129347)
                  ·
                    refine ⟨223976153646518643194021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149317435764345762129347 223976153646518643194021)
                    ·
                      refine ⟨41995528808722245598879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 223976153646518643194021 41995528808722245598879)
                      ·
                        rfl

theorem cell23_81786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_81786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81786 prefixEnd_81786 := by exact prefixLift 81786
  have htrace : WordTrace (prefixWord ++ tailWord_81786) baseStart_81786 baseEnd_81786 := by
    simpa [prefixWord, tailWord_81786, baseEnd_81786] using wordTrace_append hprefix tailTrace_81786
  have hstable : (prefixWord ++ tailWord_81786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81786).length < 2 ^ (prefixWord ++ tailWord_81786).sum := by decide
  have hdescent : baseEnd_81786 < baseStart_81786 := by decide
  rcases family_descends (prefixWord ++ tailWord_81786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81790 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_81790 : Nat := 118140960795 + 81790 * 2 ^ 59
def prefixEnd_81790 : Nat := 4983230072969 + 3 ^ 40 * 81790 * 2
def baseEnd_81790 : Nat := 41997582731340229948861

theorem tailTrace_81790 : CollatzResearch.WordTrace tailWord_81790 prefixEnd_81790 41997582731340229948861 := by
  unfold tailWord_81790
  simp only [CollatzResearch.WordTrace]
  refine ⟨372890796712034183126353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1988750915797515643340549 372890796712034183126353)
  ·
    refine ⟨279668097534025637344765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 372890796712034183126353 279668097534025637344765)
    ·
      refine ⟨104875536575259614004287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279668097534025637344765 104875536575259614004287)
      ·
        refine ⟨157313304862889421006431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104875536575259614004287 157313304862889421006431)
        ·
          refine ⟨235969957294334131509647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157313304862889421006431 235969957294334131509647)
          ·
            refine ⟨353954935941501197264471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235969957294334131509647 353954935941501197264471)
            ·
              refine ⟨530932403912251795896707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353954935941501197264471 530932403912251795896707)
              ·
                refine ⟨796398605868377693845061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530932403912251795896707 796398605868377693845061)
                ·
                  refine ⟨149324738600320817595949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796398605868377693845061 149324738600320817595949)
                  ·
                    refine ⟨55996776975120306598481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149324738600320817595949 55996776975120306598481)
                    ·
                      refine ⟨41997582731340229948861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 55996776975120306598481 41997582731340229948861)
                      ·
                        rfl

theorem cell23_81790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_81790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81790 prefixEnd_81790 := by exact prefixLift 81790
  have htrace : WordTrace (prefixWord ++ tailWord_81790) baseStart_81790 baseEnd_81790 := by
    simpa [prefixWord, tailWord_81790, baseEnd_81790] using wordTrace_append hprefix tailTrace_81790
  have hstable : (prefixWord ++ tailWord_81790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81790).length < 2 ^ (prefixWord ++ tailWord_81790).sum := by decide
  have hdescent : baseEnd_81790 < baseStart_81790 := by decide
  rcases family_descends (prefixWord ++ tailWord_81790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81796 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_81796 : Nat := 118140960795 + 81796 * 2 ^ 59
def prefixEnd_81796 : Nat := 4983230072969 + 3 ^ 40 * 81796 * 2
def baseEnd_81796 : Nat := 14000221205089068824611

theorem tailTrace_81796 : CollatzResearch.WordTrace tailWord_81796 prefixEnd_81796 14000221205089068824611 := by
  unfold tailWord_81796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491672605837268244864621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1988896807783024326486161 1491672605837268244864621)
  ·
    refine ⟨559377227188975591824233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1491672605837268244864621 559377227188975591824233)
    ·
      refine ⟨419532920391731693868175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 559377227188975591824233 419532920391731693868175)
      ·
        refine ⟨629299380587597540802263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419532920391731693868175 629299380587597540802263)
        ·
          refine ⟨943949070881396311203395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629299380587597540802263 943949070881396311203395)
          ·
            refine ⟨1415923606322094466805093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943949070881396311203395 1415923606322094466805093)
            ·
              refine ⟨265485676185392712525955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1415923606322094466805093 265485676185392712525955)
              ·
                refine ⟨398228514278089068788933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265485676185392712525955 398228514278089068788933)
                ·
                  refine ⟨74667846427141700397925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398228514278089068788933 74667846427141700397925)
                  ·
                    refine ⟨14000221205089068824611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74667846427141700397925 14000221205089068824611)
                    ·
                      rfl

theorem cell23_81796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_81796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81796 prefixEnd_81796 := by exact prefixLift 81796
  have htrace : WordTrace (prefixWord ++ tailWord_81796) baseStart_81796 baseEnd_81796 := by
    simpa [prefixWord, tailWord_81796, baseEnd_81796] using wordTrace_append hprefix tailTrace_81796
  have hstable : (prefixWord ++ tailWord_81796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81796).length < 2 ^ (prefixWord ++ tailWord_81796).sum := by decide
  have hdescent : baseEnd_81796 < baseStart_81796 := by decide
  rcases family_descends (prefixWord ++ tailWord_81796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81820 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_81820 : Nat := 118140960795 + 81820 * 2 ^ 59
def prefixEnd_81820 : Nat := 4983230072969 + 3 ^ 40 * 81820 * 2
def baseEnd_81820 : Nat := 42012987150975112573723

theorem tailTrace_81820 : CollatzResearch.WordTrace tailWord_81820 prefixEnd_81820 42012987150975112573723 := by
  unfold tailWord_81820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492110281793794294301457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1989480375725059059068609 1492110281793794294301457)
  ·
    refine ⟨1119082711345345720726093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1492110281793794294301457 1119082711345345720726093)
    ·
      refine ⟨419656016754504645272285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1119082711345345720726093 419656016754504645272285)
      ·
        refine ⟨157371006282939241977107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419656016754504645272285 157371006282939241977107)
        ·
          refine ⟨236056509424408862965661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157371006282939241977107 236056509424408862965661)
          ·
            refine ⟨88521191034153323612123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236056509424408862965661 88521191034153323612123)
            ·
              refine ⟨132781786551229985418185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88521191034153323612123 132781786551229985418185)
              ·
                refine ⟨99586339913422489063639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132781786551229985418185 99586339913422489063639)
                ·
                  refine ⟨149379509870133733595459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99586339913422489063639 149379509870133733595459)
                  ·
                    refine ⟨224069264805200600393189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149379509870133733595459 224069264805200600393189)
                    ·
                      refine ⟨42012987150975112573723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 224069264805200600393189 42012987150975112573723)
                      ·
                        rfl

theorem cell23_81820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_81820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81820 prefixEnd_81820 := by exact prefixLift 81820
  have htrace : WordTrace (prefixWord ++ tailWord_81820) baseStart_81820 baseEnd_81820 := by
    simpa [prefixWord, tailWord_81820, baseEnd_81820] using wordTrace_append hprefix tailTrace_81820
  have hstable : (prefixWord ++ tailWord_81820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81820).length < 2 ^ (prefixWord ++ tailWord_81820).sum := by decide
  have hdescent : baseEnd_81820 < baseStart_81820 := by decide
  rcases family_descends (prefixWord ++ tailWord_81820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81823 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_81823 : Nat := 118140960795 + 81823 * 2 ^ 59
def prefixEnd_81823 : Nat := 4983230072969 + 3 ^ 40 * 81823 * 2
def baseEnd_81823 : Nat := 42014527592938600836209

theorem tailTrace_81823 : CollatzResearch.WordTrace tailWord_81823 prefixEnd_81823 42014527592938600836209 := by
  unfold tailWord_81823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984329982576720100962123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1989553321717813400641415 2984329982576720100962123)
  ·
    refine ⟨4476494973865080151443185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984329982576720100962123 4476494973865080151443185)
    ·
      refine ⟨3357371230398810113582389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4476494973865080151443185 3357371230398810113582389)
      ·
        refine ⟨314753552849888448148349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3357371230398810113582389 314753552849888448148349)
        ·
          refine ⟨118032582318708168055631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314753552849888448148349 118032582318708168055631)
          ·
            refine ⟨177048873478062252083447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118032582318708168055631 177048873478062252083447)
            ·
              refine ⟨265573310217093378125171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177048873478062252083447 265573310217093378125171)
              ·
                refine ⟨398359965325640067187757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265573310217093378125171 398359965325640067187757)
                ·
                  refine ⟨149384986997115025195409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398359965325640067187757 149384986997115025195409)
                  ·
                    refine ⟨112038740247836268896557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149384986997115025195409 112038740247836268896557)
                    ·
                      refine ⟨42014527592938600836209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 112038740247836268896557 42014527592938600836209)
                      ·
                        rfl

theorem cell23_81823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_81823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81823 prefixEnd_81823 := by exact prefixLift 81823
  have htrace : WordTrace (prefixWord ++ tailWord_81823) baseStart_81823 baseEnd_81823 := by
    simpa [prefixWord, tailWord_81823, baseEnd_81823] using wordTrace_append hprefix tailTrace_81823
  have hstable : (prefixWord ++ tailWord_81823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81823).length < 2 ^ (prefixWord ++ tailWord_81823).sum := by decide
  have hdescent : baseEnd_81823 < baseStart_81823 := by decide
  rcases family_descends (prefixWord ++ tailWord_81823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81854 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_81854 : Nat := 118140960795 + 81854 * 2 ^ 59
def prefixEnd_81854 : Nat := 4983230072969 + 3 ^ 40 * 81854 * 2
def baseEnd_81854 : Nat := 42030445493227979548567

theorem tailTrace_81854 : CollatzResearch.WordTrace tailWord_81854 prefixEnd_81854 42030445493227979548567 := by
  unfold tailWord_81854
  simp only [CollatzResearch.WordTrace]
  refine ⟨373182580683051549417577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1990307096976274930227077 373182580683051549417577)
  ·
    refine ⟨279886935512288662063183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 373182580683051549417577 279886935512288662063183)
    ·
      refine ⟨419830403268432993094775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279886935512288662063183 419830403268432993094775)
      ·
        refine ⟨629745604902649489642163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419830403268432993094775 629745604902649489642163)
        ·
          refine ⟨944618407353974234463245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629745604902649489642163 944618407353974234463245)
          ·
            refine ⟨354231902757740337923717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 944618407353974234463245 354231902757740337923717)
            ·
              refine ⟨66418481767076313360697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 354231902757740337923717 66418481767076313360697)
              ·
                refine ⟨49813861325307235020523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66418481767076313360697 49813861325307235020523)
                ·
                  refine ⟨74720791987960852530785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49813861325307235020523 74720791987960852530785)
                  ·
                    refine ⟨56040593990970639398089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74720791987960852530785 56040593990970639398089)
                    ·
                      refine ⟨42030445493227979548567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56040593990970639398089 42030445493227979548567)
                      ·
                        rfl

theorem cell23_81854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_81854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81854 prefixEnd_81854 := by exact prefixLift 81854
  have htrace : WordTrace (prefixWord ++ tailWord_81854) baseStart_81854 baseEnd_81854 := by
    simpa [prefixWord, tailWord_81854, baseEnd_81854] using wordTrace_append hprefix tailTrace_81854
  have hstable : (prefixWord ++ tailWord_81854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81854).length < 2 ^ (prefixWord ++ tailWord_81854).sum := by decide
  have hdescent : baseEnd_81854 < baseStart_81854 := by decide
  rcases family_descends (prefixWord ++ tailWord_81854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81876 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_81876 : Nat := 118140960795 + 81876 * 2 ^ 59
def prefixEnd_81876 : Nat := 4983230072969 + 3 ^ 40 * 81876 * 2
def baseEnd_81876 : Nat := 42041742067626893473465

theorem tailTrace_81876 : CollatzResearch.WordTrace tailWord_81876 prefixEnd_81876 42041742067626893473465 := by
  unfold tailWord_81876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493131525692355076320741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1990842034256473435094321 1493131525692355076320741)
  ·
    refine ⟨279962161067316576810139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1493131525692355076320741 279962161067316576810139)
    ·
      refine ⟨419943241600974865215209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279962161067316576810139 419943241600974865215209)
      ·
        refine ⟨314957431200731148911407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419943241600974865215209 314957431200731148911407)
        ·
          refine ⟨472436146801096723367111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314957431200731148911407 472436146801096723367111)
          ·
            refine ⟨708654220201645085050667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472436146801096723367111 708654220201645085050667)
            ·
              refine ⟨1062981330302467627576001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708654220201645085050667 1062981330302467627576001)
              ·
                refine ⟨797235997726850720682001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062981330302467627576001 797235997726850720682001)
                ·
                  refine ⟨597926998295138040511501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797235997726850720682001 597926998295138040511501)
                  ·
                    refine ⟨224222624360676765191813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597926998295138040511501 224222624360676765191813)
                    ·
                      refine ⟨42041742067626893473465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 224222624360676765191813 42041742067626893473465)
                      ·
                        rfl

theorem cell23_81876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_81876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81876 prefixEnd_81876 := by exact prefixLift 81876
  have htrace : WordTrace (prefixWord ++ tailWord_81876) baseStart_81876 baseEnd_81876 := by
    simpa [prefixWord, tailWord_81876, baseEnd_81876] using wordTrace_append hprefix tailTrace_81876
  have hstable : (prefixWord ++ tailWord_81876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81876).length < 2 ^ (prefixWord ++ tailWord_81876).sum := by decide
  have hdescent : baseEnd_81876 < baseStart_81876 := by decide
  rcases family_descends (prefixWord ++ tailWord_81876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81916 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 7]
def baseStart_81916 : Nat := 118140960795 + 81916 * 2 ^ 59
def prefixEnd_81916 : Nat := 4983230072969 + 3 ^ 40 * 81916 * 2
def baseEnd_81916 : Nat := 4673586810422970774809

theorem tailTrace_81916 : CollatzResearch.WordTrace tailWord_81916 prefixEnd_81916 4673586810422970774809 := by
  unfold tailWord_81916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493860985619898492048801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1991814647493197989398401 1493860985619898492048801)
  ·
    refine ⟨1120395739214923869036601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1493860985619898492048801 1120395739214923869036601)
    ·
      refine ⟨840296804411192901777451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1120395739214923869036601 840296804411192901777451)
      ·
        refine ⟨1260445206616789352666177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840296804411192901777451 1260445206616789352666177)
        ·
          refine ⟨945333904962592014499633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260445206616789352666177 945333904962592014499633)
          ·
            refine ⟨709000428721944010874725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945333904962592014499633 709000428721944010874725)
            ·
              refine ⟨132937580385364502039011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 709000428721944010874725 132937580385364502039011)
              ·
                refine ⟨199406370578046753058517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132937580385364502039011 199406370578046753058517)
                ·
                  refine ⟨4673586810422970774809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 199406370578046753058517 4673586810422970774809)
                  ·
                    rfl

theorem cell23_81916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_81916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81916 prefixEnd_81916 := by exact prefixLift 81916
  have htrace : WordTrace (prefixWord ++ tailWord_81916) baseStart_81916 baseEnd_81916 := by
    simpa [prefixWord, tailWord_81916, baseEnd_81916] using wordTrace_append hprefix tailTrace_81916
  have hstable : (prefixWord ++ tailWord_81916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81916).length < 2 ^ (prefixWord ++ tailWord_81916).sum := by decide
  have hdescent : baseEnd_81916 < baseStart_81916 := by decide
  rcases family_descends (prefixWord ++ tailWord_81916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81946 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_81946 : Nat := 118140960795 + 81946 * 2 ^ 59
def prefixEnd_81946 : Nat := 4983230072969 + 3 ^ 40 * 81946 * 2
def baseEnd_81946 : Nat := 14025895237813873199381

theorem tailTrace_81946 : CollatzResearch.WordTrace tailWord_81946 prefixEnd_81946 14025895237813873199381 := by
  unfold tailWord_81946
  simp only [CollatzResearch.WordTrace]
  refine ⟨747204040282778026922423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1992544107420741405126461 747204040282778026922423)
  ·
    refine ⟨1120806060424167040383635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747204040282778026922423 1120806060424167040383635)
    ·
      refine ⟨1681209090636250560575453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1120806060424167040383635 1681209090636250560575453)
      ·
        refine ⟨630453408988593960215795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1681209090636250560575453 630453408988593960215795)
        ·
          refine ⟨945680113482890940323693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630453408988593960215795 945680113482890940323693)
          ·
            refine ⟨354630042556084102621385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 945680113482890940323693 354630042556084102621385)
            ·
              refine ⟨265972531917063076966039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354630042556084102621385 265972531917063076966039)
              ·
                refine ⟨398958797875594615449059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265972531917063076966039 398958797875594615449059)
                ·
                  refine ⟨598438196813391923173589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398958797875594615449059 598438196813391923173589)
                  ·
                    refine ⟨14025895237813873199381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 598438196813391923173589 14025895237813873199381)
                    ·
                      rfl

theorem cell23_81946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_81946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81946 prefixEnd_81946 := by exact prefixLift 81946
  have htrace : WordTrace (prefixWord ++ tailWord_81946) baseStart_81946 baseEnd_81946 := by
    simpa [prefixWord, tailWord_81946, baseEnd_81946] using wordTrace_append hprefix tailTrace_81946
  have hstable : (prefixWord ++ tailWord_81946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81946).length < 2 ^ (prefixWord ++ tailWord_81946).sum := by decide
  have hdescent : baseEnd_81946 < baseStart_81946 := by decide
  rcases family_descends (prefixWord ++ tailWord_81946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81983 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 2, 4, 2]
def baseStart_81983 : Nat := 118140960795 + 81983 * 2 ^ 59
def prefixEnd_81983 : Nat := 4983230072969 + 3 ^ 40 * 81983 * 2
def baseEnd_81983 : Nat := 42096684497657974835473

theorem tailTrace_81983 : CollatzResearch.WordTrace tailWord_81983 prefixEnd_81983 42096684497657974835473 := by
  unfold tailWord_81983
  simp only [CollatzResearch.WordTrace]
  refine ⟨2990165661997067426786603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1993443774664711617857735 2990165661997067426786603)
  ·
    refine ⟨4485248492995601140179905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2990165661997067426786603 4485248492995601140179905)
    ·
      refine ⟨3363936369746700855134929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4485248492995601140179905 3363936369746700855134929)
      ·
        refine ⟨2522952277310025641351197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3363936369746700855134929 2522952277310025641351197)
        ·
          refine ⟨946107103991259615506699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2522952277310025641351197 946107103991259615506699)
          ·
            refine ⟨1419160655986889423260049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946107103991259615506699 1419160655986889423260049)
            ·
              refine ⟨1064370491990167067445037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419160655986889423260049 1064370491990167067445037)
              ·
                refine ⟨399138934496312650291889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064370491990167067445037 399138934496312650291889)
                ·
                  refine ⟨299354200872234487718917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399138934496312650291889 299354200872234487718917)
                  ·
                    refine ⟨56128912663543966447297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 299354200872234487718917 56128912663543966447297)
                    ·
                      refine ⟨42096684497657974835473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56128912663543966447297 42096684497657974835473)
                      ·
                        rfl

theorem cell23_81983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_81983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81983 prefixEnd_81983 := by exact prefixLift 81983
  have htrace : WordTrace (prefixWord ++ tailWord_81983) baseStart_81983 baseEnd_81983 := by
    simpa [prefixWord, tailWord_81983, baseEnd_81983] using wordTrace_append hprefix tailTrace_81983
  have hstable : (prefixWord ++ tailWord_81983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81983).length < 2 ^ (prefixWord ++ tailWord_81983).sum := by decide
  have hdescent : baseEnd_81983 < baseStart_81983 := by decide
  rcases family_descends (prefixWord ++ tailWord_81983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81996 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_81996 : Nat := 118140960795 + 81996 * 2 ^ 59
def prefixEnd_81996 : Nat := 4983230072969 + 3 ^ 40 * 81996 * 2
def baseEnd_81996 : Nat := 42103359746166423972913

theorem tailTrace_81996 : CollatzResearch.WordTrace tailWord_81996 prefixEnd_81996 42103359746166423972913 := by
  unfold tailWord_81996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495319905474985323504921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1993759873966647098006561 1495319905474985323504921)
  ·
    refine ⟨1121489929106238992628691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1495319905474985323504921 1121489929106238992628691)
    ·
      refine ⟨1682234893659358488943037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1121489929106238992628691 1682234893659358488943037)
      ·
        refine ⟨630838085122259433353639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1682234893659358488943037 630838085122259433353639)
        ·
          refine ⟨946257127683389150030459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630838085122259433353639 946257127683389150030459)
          ·
            refine ⟨1419385691525083725045689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946257127683389150030459 1419385691525083725045689)
            ·
              refine ⟨1064539268643812793784267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419385691525083725045689 1064539268643812793784267)
              ·
                refine ⟨1596808902965719190676401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064539268643812793784267 1596808902965719190676401)
                ·
                  refine ⟨1197606677224289393007301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596808902965719190676401 1197606677224289393007301)
                  ·
                    refine ⟨224551251979554261188869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1197606677224289393007301 224551251979554261188869)
                    ·
                      refine ⟨42103359746166423972913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 224551251979554261188869 42103359746166423972913)
                      ·
                        rfl

theorem cell23_81996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_81996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_81996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_81996 prefixEnd_81996 := by exact prefixLift 81996
  have htrace : WordTrace (prefixWord ++ tailWord_81996) baseStart_81996 baseEnd_81996 := by
    simpa [prefixWord, tailWord_81996, baseEnd_81996] using wordTrace_append hprefix tailTrace_81996
  have hstable : (prefixWord ++ tailWord_81996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81996).length < 2 ^ (prefixWord ++ tailWord_81996).sum := by decide
  have hdescent : baseEnd_81996 < baseStart_81996 := by decide
  rcases family_descends (prefixWord ++ tailWord_81996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82010 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_82010 : Nat := 118140960795 + 82010 * 2 ^ 59
def prefixEnd_82010 : Nat := 4983230072969 + 3 ^ 40 * 82010 * 2
def baseEnd_82010 : Nat := 14036849491776456399283

theorem tailTrace_82010 : CollatzResearch.WordTrace tailWord_82010 prefixEnd_82010 14036849491776456399283 := by
  unfold tailWord_82010
  simp only [CollatzResearch.WordTrace]
  refine ⟨747787608224812759504871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1994100288599500692012989 747787608224812759504871)
  ·
    refine ⟨1121681412337219139257307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747787608224812759504871 1121681412337219139257307)
    ·
      refine ⟨1682522118505828708885961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1121681412337219139257307 1682522118505828708885961)
      ·
        refine ⟨1261891588879371531664471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1682522118505828708885961 1261891588879371531664471)
        ·
          refine ⟨1892837383319057297496707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261891588879371531664471 1892837383319057297496707)
          ·
            refine ⟨2839256074978585946245061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892837383319057297496707 2839256074978585946245061)
            ·
              refine ⟨532360514058484864920949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2839256074978585946245061 532360514058484864920949)
              ·
                refine ⟨49908798192982956086339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532360514058484864920949 49908798192982956086339)
                ·
                  refine ⟨74863197289474434129509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49908798192982956086339 74863197289474434129509)
                  ·
                    refine ⟨14036849491776456399283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74863197289474434129509 14036849491776456399283)
                    ·
                      rfl

theorem cell23_82010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_82010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82010 prefixEnd_82010 := by exact prefixLift 82010
  have htrace : WordTrace (prefixWord ++ tailWord_82010) baseStart_82010 baseEnd_82010 := by
    simpa [prefixWord, tailWord_82010, baseEnd_82010] using wordTrace_append hprefix tailTrace_82010
  have hstable : (prefixWord ++ tailWord_82010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82010).length < 2 ^ (prefixWord ++ tailWord_82010).sum := by decide
  have hdescent : baseEnd_82010 < baseStart_82010 := by decide
  rcases family_descends (prefixWord ++ tailWord_82010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82023 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 6]
def baseStart_82023 : Nat := 118140960795 + 82023 * 2 ^ 59
def prefixEnd_82023 : Nat := 4983230072969 + 3 ^ 40 * 82023 * 2
def baseEnd_82023 : Nat := 4679691524870868703921

theorem tailTrace_82023 : CollatzResearch.WordTrace tailWord_82023 prefixEnd_82023 4679691524870868703921 := by
  unfold tailWord_82023
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991624581852154258242723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1994416387901436172161815 2991624581852154258242723)
  ·
    refine ⟨4487436872778231387364085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2991624581852154258242723 4487436872778231387364085)
    ·
      refine ⟨420697206822959192565383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4487436872778231387364085 420697206822959192565383)
      ·
        refine ⟨631045810234438788848075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420697206822959192565383 631045810234438788848075)
        ·
          refine ⟨946568715351658183272113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631045810234438788848075 946568715351658183272113)
          ·
            refine ⟨709926536513743637454085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946568715351658183272113 709926536513743637454085)
            ·
              refine ⟨133111225596326932022641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 709926536513743637454085 133111225596326932022641)
              ·
                refine ⟨99833419197245199016981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133111225596326932022641 99833419197245199016981)
                ·
                  refine ⟨4679691524870868703921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99833419197245199016981 4679691524870868703921)
                  ·
                    rfl

theorem cell23_82023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 6].length) (baseStart_82023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82023 prefixEnd_82023 := by exact prefixLift 82023
  have htrace : WordTrace (prefixWord ++ tailWord_82023) baseStart_82023 baseEnd_82023 := by
    simpa [prefixWord, tailWord_82023, baseEnd_82023] using wordTrace_append hprefix tailTrace_82023
  have hstable : (prefixWord ++ tailWord_82023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82023).length < 2 ^ (prefixWord ++ tailWord_82023).sum := by decide
  have hdescent : baseEnd_82023 < baseStart_82023 := by decide
  rcases family_descends (prefixWord ++ tailWord_82023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82053 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_82053 : Nat := 118140960795 + 82053 * 2 ^ 59
def prefixEnd_82053 : Nat := 4983230072969 + 3 ^ 40 * 82053 * 2
def baseEnd_82053 : Nat := 14044209381157566986717

theorem tailTrace_82053 : CollatzResearch.WordTrace tailWord_82053 prefixEnd_82053 14044209381157566986717 := by
  unfold tailWord_82053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992718771743469381834813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1995145847828979587889875 2992718771743469381834813)
  ·
    refine ⟨1122269539403801018188055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2992718771743469381834813 1122269539403801018188055)
    ·
      refine ⟨1683404309105701527282083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122269539403801018188055 1683404309105701527282083)
      ·
        refine ⟨2525106463658552290923125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683404309105701527282083 2525106463658552290923125)
        ·
          refine ⟨236728730967989277274043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2525106463658552290923125 236728730967989277274043)
          ·
            refine ⟨355093096451983915911065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236728730967989277274043 355093096451983915911065)
            ·
              refine ⟨266319822338987936933299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355093096451983915911065 266319822338987936933299)
              ·
                refine ⟨399479733508481905399949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266319822338987936933299 399479733508481905399949)
                ·
                  refine ⟨149804900065680714524981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399479733508481905399949 149804900065680714524981)
                  ·
                    refine ⟨14044209381157566986717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149804900065680714524981 14044209381157566986717)
                    ·
                      rfl

theorem cell23_82053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_82053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82053 prefixEnd_82053 := by exact prefixLift 82053
  have htrace : WordTrace (prefixWord ++ tailWord_82053) baseStart_82053 baseEnd_82053 := by
    simpa [prefixWord, tailWord_82053, baseEnd_82053] using wordTrace_append hprefix tailTrace_82053
  have hstable : (prefixWord ++ tailWord_82053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82053).length < 2 ^ (prefixWord ++ tailWord_82053).sum := by decide
  have hdescent : baseEnd_82053 < baseStart_82053 := by decide
  rcases family_descends (prefixWord ++ tailWord_82053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82073 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 8, 2]
def baseStart_82073 : Nat := 118140960795 + 82073 * 2 ^ 59
def prefixEnd_82073 : Nat := 4983230072969 + 3 ^ 40 * 82073 * 2
def baseEnd_82073 : Nat := 42142897756562622710059

theorem tailTrace_82073 : CollatzResearch.WordTrace tailWord_82073 prefixEnd_82073 42142897756562622710059 := by
  unfold tailWord_82073
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993448231671012797562873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1995632154447341865041915 2993448231671012797562873)
  ·
    refine ⟨2245086173753259598172155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2993448231671012797562873 2245086173753259598172155)
    ·
      refine ⟨3367629260629889397258233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2245086173753259598172155 3367629260629889397258233)
      ·
        refine ⟨2525721945472417047943675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3367629260629889397258233 2525721945472417047943675)
        ·
          refine ⟨3788582918208625571915513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525721945472417047943675 3788582918208625571915513)
          ·
            refine ⟨2841437188656469178936635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3788582918208625571915513 2841437188656469178936635)
            ·
              refine ⟨4262155782984703768404953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841437188656469178936635 4262155782984703768404953)
              ·
                refine ⟨3196616837238527826303715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262155782984703768404953 3196616837238527826303715)
                ·
                  refine ⟨4794925255857791739455573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3196616837238527826303715 4794925255857791739455573)
                  ·
                    refine ⟨56190530342083496946745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4794925255857791739455573 56190530342083496946745)
                    ·
                      refine ⟨42142897756562622710059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56190530342083496946745 42142897756562622710059)
                      ·
                        rfl

theorem cell23_82073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_82073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82073 prefixEnd_82073 := by exact prefixLift 82073
  have htrace : WordTrace (prefixWord ++ tailWord_82073) baseStart_82073 baseEnd_82073 := by
    simpa [prefixWord, tailWord_82073, baseEnd_82073] using wordTrace_append hprefix tailTrace_82073
  have hstable : (prefixWord ++ tailWord_82073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82073).length < 2 ^ (prefixWord ++ tailWord_82073).sum := by decide
  have hdescent : baseEnd_82073 < baseStart_82073 := by decide
  rcases family_descends (prefixWord ++ tailWord_82073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82103 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_82103 : Nat := 118140960795 + 82103 * 2 ^ 59
def prefixEnd_82103 : Nat := 4983230072969 + 3 ^ 40 * 82103 * 2
def baseEnd_82103 : Nat := 42158302176197505334921

theorem tailTrace_82103 : CollatzResearch.WordTrace tailWord_82103 prefixEnd_82103 42158302176197505334921 := by
  unfold tailWord_82103
  simp only [CollatzResearch.WordTrace]
  refine ⟨2994542421562327921154963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1996361614374885280769975 2994542421562327921154963)
  ·
    refine ⟨4491813632343491881732445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2994542421562327921154963 4491813632343491881732445)
    ·
      refine ⟨1684430112128809455649667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4491813632343491881732445 1684430112128809455649667)
      ·
        refine ⟨2526645168193214183474501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684430112128809455649667 2526645168193214183474501)
        ·
          refine ⟨473745969036227659401469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2526645168193214183474501 473745969036227659401469)
          ·
            refine ⟨177654738388585372275551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 473745969036227659401469 177654738388585372275551)
            ·
              refine ⟨266482107582878058413327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177654738388585372275551 266482107582878058413327)
              ·
                refine ⟨399723161374317087619991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266482107582878058413327 399723161374317087619991)
                ·
                  refine ⟨599584742061475631429987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399723161374317087619991 599584742061475631429987)
                  ·
                    refine ⟨899377113092213447144981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 599584742061475631429987 899377113092213447144981)
                    ·
                      refine ⟨42158302176197505334921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 899377113092213447144981 42158302176197505334921)
                      ·
                        rfl

theorem cell23_82103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_82103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82103 prefixEnd_82103 := by exact prefixLift 82103
  have htrace : WordTrace (prefixWord ++ tailWord_82103) baseStart_82103 baseEnd_82103 := by
    simpa [prefixWord, tailWord_82103, baseEnd_82103] using wordTrace_append hprefix tailTrace_82103
  have hstable : (prefixWord ++ tailWord_82103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82103).length < 2 ^ (prefixWord ++ tailWord_82103).sum := by decide
  have hdescent : baseEnd_82103 < baseStart_82103 := by decide
  rcases family_descends (prefixWord ++ tailWord_82103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
