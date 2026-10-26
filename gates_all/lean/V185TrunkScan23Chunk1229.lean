import V185TrunkScan23Chunk1228

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7282766 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_7282766 : Nat := 118140960795 + 7282766 * 2 ^ 59
def prefixEnd_7282766 : Nat := 4983230072969 + 3 ^ 40 * 7282766 * 2
def baseEnd_7282766 : Nat := 415506605802439819803575

theorem tailTrace_7282766 : CollatzResearch.WordTrace tailWord_7282766 prefixEnd_7282766 415506605802439819803575 := by
  unfold tailWord_7282766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33203037241723756781767519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177082865289193369502760101 33203037241723756781767519)
  ·
    refine ⟨49804555862585635172651279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33203037241723756781767519 49804555862585635172651279)
    ·
      refine ⟨74706833793878452758976919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49804555862585635172651279 74706833793878452758976919)
      ·
        refine ⟨112060250690817679138465379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74706833793878452758976919 112060250690817679138465379)
        ·
          refine ⟨168090376036226518707698069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112060250690817679138465379 168090376036226518707698069)
          ·
            refine ⟨7879236376698118064423347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168090376036226518707698069 7879236376698118064423347)
            ·
              refine ⟨11818854565047177096635021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879236376698118064423347 11818854565047177096635021)
              ·
                refine ⟨4432070461892691411238133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818854565047177096635021 4432070461892691411238133)
                ·
                  refine ⟨415506605802439819803575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4432070461892691411238133 415506605802439819803575)
                  ·
                    rfl

theorem cell23_7282766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_7282766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282766 prefixEnd_7282766 := by exact prefixLift 7282766
  have htrace : WordTrace (prefixWord ++ tailWord_7282766) baseStart_7282766 baseEnd_7282766 := by
    simpa [prefixWord, tailWord_7282766, baseEnd_7282766] using wordTrace_append hprefix tailTrace_7282766
  have hstable : (prefixWord ++ tailWord_7282766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282766).length < 2 ^ (prefixWord ++ tailWord_7282766).sum := by decide
  have hdescent : baseEnd_7282766 < baseStart_7282766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282772 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_7282772 : Nat := 118140960795 + 7282772 * 2 ^ 59
def prefixEnd_7282772 : Nat := 4983230072969 + 3 ^ 40 * 7282772 * 2
def baseEnd_7282772 : Nat := 3739562533105885354757147

theorem tailTrace_7282772 : CollatzResearch.WordTrace tailWord_7282772 prefixEnd_7282772 3739562533105885354757147 := by
  unfold tailWord_7282772
  simp only [CollatzResearch.WordTrace]
  refine ⟨132812258385884158639429285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177083011181178878185905713 132812258385884158639429285)
  ·
    refine ⟨24902298447353279744892991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132812258385884158639429285 24902298447353279744892991)
    ·
      refine ⟨37353447671029919617339487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24902298447353279744892991 37353447671029919617339487)
      ·
        refine ⟨56030171506544879426009231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37353447671029919617339487 56030171506544879426009231)
        ·
          refine ⟨84045257259817319139013847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56030171506544879426009231 84045257259817319139013847)
          ·
            refine ⟨126067885889725978708520771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84045257259817319139013847 126067885889725978708520771)
            ·
              refine ⟨189101828834588968062781157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126067885889725978708520771 189101828834588968062781157)
              ·
                refine ⟨35456592906485431511771467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189101828834588968062781157 35456592906485431511771467)
                ·
                  refine ⟨53184889359728147267657201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35456592906485431511771467 53184889359728147267657201)
                  ·
                    refine ⟨39888667019796110450742901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53184889359728147267657201 39888667019796110450742901)
                    ·
                      refine ⟨3739562533105885354757147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39888667019796110450742901 3739562533105885354757147)
                      ·
                        rfl

theorem cell23_7282772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_7282772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282772 prefixEnd_7282772 := by exact prefixLift 7282772
  have htrace : WordTrace (prefixWord ++ tailWord_7282772) baseStart_7282772 baseEnd_7282772 := by
    simpa [prefixWord, tailWord_7282772, baseEnd_7282772] using wordTrace_append hprefix tailTrace_7282772
  have hstable : (prefixWord ++ tailWord_7282772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282772).length < 2 ^ (prefixWord ++ tailWord_7282772).sum := by decide
  have hdescent : baseEnd_7282772 < baseStart_7282772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282819 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 3]
def baseStart_7282819 : Nat := 118140960795 + 7282819 * 2 ^ 59
def prefixEnd_7282819 : Nat := 4983230072969 + 3 ^ 40 * 7282819 * 2
def baseEnd_7282819 : Nat := 3739586666696646670869431

theorem tailTrace_7282819 : CollatzResearch.WordTrace tailWord_7282819 prefixEnd_7282819 3739586666696646670869431 := by
  unfold tailWord_7282819
  simp only [CollatzResearch.WordTrace]
  refine ⟨265626231002598044305819511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177084154001732029537213007 265626231002598044305819511)
  ·
    refine ⟨398439346503897066458729267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265626231002598044305819511 398439346503897066458729267)
    ·
      refine ⟨597659019755845599688093901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398439346503897066458729267 597659019755845599688093901)
      ·
        refine ⟨224122132408442099883035213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597659019755845599688093901 224122132408442099883035213)
        ·
          refine ⟨84045799653165787456138205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224122132408442099883035213 84045799653165787456138205)
          ·
            refine ⟨31517174869937170296051827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84045799653165787456138205 31517174869937170296051827)
            ·
              refine ⟨47275762304905755444077741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31517174869937170296051827 47275762304905755444077741)
              ·
                refine ⟨17728410864339658291529153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47275762304905755444077741 17728410864339658291529153)
                ·
                  refine ⟨13296308148254743718646865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17728410864339658291529153 13296308148254743718646865)
                  ·
                    refine ⟨9972231111191057788985149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13296308148254743718646865 9972231111191057788985149)
                    ·
                      refine ⟨3739586666696646670869431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972231111191057788985149 3739586666696646670869431)
                      ·
                        rfl

theorem cell23_7282819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_7282819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282819 prefixEnd_7282819 := by exact prefixLift 7282819
  have htrace : WordTrace (prefixWord ++ tailWord_7282819) baseStart_7282819 baseEnd_7282819 := by
    simpa [prefixWord, tailWord_7282819, baseEnd_7282819] using wordTrace_append hprefix tailTrace_7282819
  have hstable : (prefixWord ++ tailWord_7282819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282819).length < 2 ^ (prefixWord ++ tailWord_7282819).sum := by decide
  have hdescent : baseEnd_7282819 < baseStart_7282819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282866 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_7282866 : Nat := 118140960795 + 7282866 * 2 ^ 59
def prefixEnd_7282866 : Nat := 4983230072969 + 3 ^ 40 * 7282866 * 2
def baseEnd_7282866 : Nat := 3739610800287407986981715

theorem tailTrace_7282866 : CollatzResearch.WordTrace tailWord_7282866 prefixEnd_7282866 3739610800287407986981715 := by
  unfold tailWord_7282866
  simp only [CollatzResearch.WordTrace]
  refine ⟨66406986308356942833195113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177085296822285180888520301 66406986308356942833195113)
  ·
    refine ⟨49805239731267707124896335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66406986308356942833195113 49805239731267707124896335)
    ·
      refine ⟨74707859596901560687344503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49805239731267707124896335 74707859596901560687344503)
      ·
        refine ⟨112061789395352341031016755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74707859596901560687344503 112061789395352341031016755)
        ·
          refine ⟨168092684093028511546525133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112061789395352341031016755 168092684093028511546525133)
          ·
            refine ⟨63034756534885691829946925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168092684093028511546525133 63034756534885691829946925)
            ·
              refine ⟨23638033700582134436230097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63034756534885691829946925 23638033700582134436230097)
              ·
                refine ⟨17728525275436600827172573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23638033700582134436230097 17728525275436600827172573)
                ·
                  refine ⟨6648196978288725310189715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17728525275436600827172573 6648196978288725310189715)
                  ·
                    refine ⟨9972295467433087965284573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6648196978288725310189715 9972295467433087965284573)
                    ·
                      refine ⟨3739610800287407986981715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972295467433087965284573 3739610800287407986981715)
                      ·
                        rfl

theorem cell23_7282866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_7282866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282866 prefixEnd_7282866 := by exact prefixLift 7282866
  have htrace : WordTrace (prefixWord ++ tailWord_7282866) baseStart_7282866 baseEnd_7282866 := by
    simpa [prefixWord, tailWord_7282866, baseEnd_7282866] using wordTrace_append hprefix tailTrace_7282866
  have hstable : (prefixWord ++ tailWord_7282866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282866).length < 2 ^ (prefixWord ++ tailWord_7282866).sum := by decide
  have hdescent : baseEnd_7282866 < baseStart_7282866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282912 : List Nat := [2, 1, 1, 3, 1, 3, 2, 10]
def baseStart_7282912 : Nat := 118140960795 + 7282912 * 2 ^ 59
def prefixEnd_7282912 : Nat := 4983230072969 + 3 ^ 40 * 7282912 * 2
def baseEnd_7282912 : Nat := 138504978533241289148389

theorem tailTrace_7282912 : CollatzResearch.WordTrace tailWord_7282912 prefixEnd_7282912 138504978533241289148389 := by
  unfold tailWord_7282912
  simp only [CollatzResearch.WordTrace]
  refine ⟨132814811495630560594477495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177086415327507414125969993 132814811495630560594477495)
  ·
    refine ⟨199222217243445840891716243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132814811495630560594477495 199222217243445840891716243)
    ·
      refine ⟨298833325865168761337574365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199222217243445840891716243 298833325865168761337574365)
      ·
        refine ⟨112062497199438285501590387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298833325865168761337574365 112062497199438285501590387)
        ·
          refine ⟨168093745799157428252385581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112062497199438285501590387 168093745799157428252385581)
          ·
            refine ⟨63035154674684035594644593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168093745799157428252385581 63035154674684035594644593)
            ·
              refine ⟨47276366006013026695983445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63035154674684035594644593 47276366006013026695983445)
              ·
                refine ⟨138504978533241289148389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47276366006013026695983445 138504978533241289148389)
                ·
                  rfl

theorem cell23_7282912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 10].length) (baseStart_7282912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282912 prefixEnd_7282912 := by exact prefixLift 7282912
  have htrace : WordTrace (prefixWord ++ tailWord_7282912) baseStart_7282912 baseEnd_7282912 := by
    simpa [prefixWord, tailWord_7282912, baseEnd_7282912] using wordTrace_append hprefix tailTrace_7282912
  have hstable : (prefixWord ++ tailWord_7282912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282912).length < 2 ^ (prefixWord ++ tailWord_7282912).sum := by decide
  have hdescent : baseEnd_7282912 < baseStart_7282912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282929 : List Nat := [1, 2, 2, 2, 2, 1, 6, 7]
def baseStart_7282929 : Nat := 118140960795 + 7282929 * 2 ^ 59
def prefixEnd_7282929 : Nat := 4983230072969 + 3 ^ 40 * 7282929 * 2
def baseEnd_7282929 : Nat := 138505301835875601499775

theorem tailTrace_7282929 : CollatzResearch.WordTrace tailWord_7282929 prefixEnd_7282929 138505301835875601499775 := by
  unfold tailWord_7282929
  simp only [CollatzResearch.WordTrace]
  refine ⟨265630243032199533092323841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177086828688133022061549227 265630243032199533092323841)
  ·
    refine ⟨199222682274149649819242881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265630243032199533092323841 199222682274149649819242881)
    ·
      refine ⟨149417011705612237364432161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199222682274149649819242881 149417011705612237364432161)
      ·
        refine ⟨112062758779209178023324121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149417011705612237364432161 112062758779209178023324121)
        ·
          refine ⟨84047069084406883517493091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112062758779209178023324121 84047069084406883517493091)
          ·
            refine ⟨126070603626610325276239637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84047069084406883517493091 126070603626610325276239637)
            ·
              refine ⟨5909559544997358997323733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126070603626610325276239637 5909559544997358997323733)
              ·
                refine ⟨138505301835875601499775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5909559544997358997323733 138505301835875601499775)
                ·
                  rfl

theorem cell23_7282929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 7].length) (baseStart_7282929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282929 prefixEnd_7282929 := by exact prefixLift 7282929
  have htrace : WordTrace (prefixWord ++ tailWord_7282929) baseStart_7282929 baseEnd_7282929 := by
    simpa [prefixWord, tailWord_7282929, baseEnd_7282929] using wordTrace_append hprefix tailTrace_7282929
  have hstable : (prefixWord ++ tailWord_7282929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282929).length < 2 ^ (prefixWord ++ tailWord_7282929).sum := by decide
  have hdescent : baseEnd_7282929 < baseStart_7282929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282946 : List Nat := [3, 4, 1, 1, 2, 3, 9]
def baseStart_7282946 : Nat := 118140960795 + 7282946 * 2 ^ 59
def prefixEnd_7282946 : Nat := 4983230072969 + 3 ^ 40 * 7282946 * 2
def baseEnd_7282946 : Nat := 46168541712836637950387

theorem tailTrace_7282946 : CollatzResearch.WordTrace tailWord_7282946 prefixEnd_7282946 46168541712836637950387 := by
  unfold tailWord_7282946
  simp only [CollatzResearch.WordTrace]
  refine ⟨66407715768284486248923173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177087242048758629997128461 66407715768284486248923173)
  ·
    refine ⟨12451446706553341171673095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66407715768284486248923173 12451446706553341171673095)
    ·
      refine ⟨18677170059830011757509643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12451446706553341171673095 18677170059830011757509643)
      ·
        refine ⟨28015755089745017636264465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677170059830011757509643 28015755089745017636264465)
        ·
          refine ⟨21011816317308763227198349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28015755089745017636264465 21011816317308763227198349)
          ·
            refine ⟨7879431118990786210199381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21011816317308763227198349 7879431118990786210199381)
            ·
              refine ⟨46168541712836637950387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7879431118990786210199381 46168541712836637950387)
              ·
                rfl

theorem cell23_7282946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 9].length) (baseStart_7282946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282946 prefixEnd_7282946 := by exact prefixLift 7282946
  have htrace : WordTrace (prefixWord ++ tailWord_7282946) baseStart_7282946 baseEnd_7282946 := by
    simpa [prefixWord, tailWord_7282946, baseEnd_7282946] using wordTrace_append hprefix tailTrace_7282946
  have hstable : (prefixWord ++ tailWord_7282946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282946).length < 2 ^ (prefixWord ++ tailWord_7282946).sum := by decide
  have hdescent : baseEnd_7282946 < baseStart_7282946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282956 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_7282956 : Nat := 118140960795 + 7282956 * 2 ^ 59
def prefixEnd_7282956 : Nat := 4983230072969 + 3 ^ 40 * 7282956 * 2
def baseEnd_7282956 : Nat := 3739657013546312634856301

theorem tailTrace_7282956 : CollatzResearch.WordTrace tailWord_7282956 prefixEnd_7282956 3739657013546312634856301 := by
  unfold tailWord_7282956
  simp only [CollatzResearch.WordTrace]
  refine ⟨132815613901550858351778361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177087485202067811135704481 132815613901550858351778361)
  ·
    refine ⟨99611710426163143763833771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132815613901550858351778361 99611710426163143763833771)
    ·
      refine ⟨149417565639244715645750657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99611710426163143763833771 149417565639244715645750657)
      ·
        refine ⟨112063174229433536734312993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149417565639244715645750657 112063174229433536734312993)
        ·
          refine ⟨84047380672075152550734745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112063174229433536734312993 84047380672075152550734745)
          ·
            refine ⟨63035535504056364413051059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84047380672075152550734745 63035535504056364413051059)
            ·
              refine ⟨94553303256084546619576589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63035535504056364413051059 94553303256084546619576589)
              ·
                refine ⟨35457488721031704982341221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94553303256084546619576589 35457488721031704982341221)
                ·
                  refine ⟨6648279135193444684188979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35457488721031704982341221 6648279135193444684188979)
                  ·
                    refine ⟨9972418702790167026283469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6648279135193444684188979 9972418702790167026283469)
                    ·
                      refine ⟨3739657013546312634856301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972418702790167026283469 3739657013546312634856301)
                      ·
                        rfl

theorem cell23_7282956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_7282956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282956 prefixEnd_7282956 := by exact prefixLift 7282956
  have htrace : WordTrace (prefixWord ++ tailWord_7282956) baseStart_7282956 baseEnd_7282956 := by
    simpa [prefixWord, tailWord_7282956, baseEnd_7282956] using wordTrace_append hprefix tailTrace_7282956
  have hstable : (prefixWord ++ tailWord_7282956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282956).length < 2 ^ (prefixWord ++ tailWord_7282956).sum := by decide
  have hdescent : baseEnd_7282956 < baseStart_7282956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282990 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7282990 : Nat := 118140960795 + 7282990 * 2 ^ 59
def prefixEnd_7282990 : Nat := 4983230072969 + 3 ^ 40 * 7282990 * 2
def baseEnd_7282990 : Nat := 3739674471888565501831145

theorem tailTrace_7282990 : CollatzResearch.WordTrace tailWord_7282990 prefixEnd_7282990 3739674471888565501831145 := by
  unfold tailWord_7282990
  simp only [CollatzResearch.WordTrace]
  refine ⟨33204058485622317563786803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177088311923319027006862949 33204058485622317563786803)
  ·
    refine ⟨49806087728433476345680205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33204058485622317563786803 49806087728433476345680205)
    ·
      refine ⟨18677282898162553629630077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49806087728433476345680205 18677282898162553629630077)
      ·
        refine ⟨7003981086810957611111279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18677282898162553629630077 7003981086810957611111279)
        ·
          refine ⟨10505971630216436416666919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7003981086810957611111279 10505971630216436416666919)
          ·
            refine ⟨15758957445324654625000379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10505971630216436416666919 15758957445324654625000379)
            ·
              refine ⟨23638436167986981937500569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15758957445324654625000379 23638436167986981937500569)
              ·
                refine ⟨17728827125990236453125427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23638436167986981937500569 17728827125990236453125427)
                ·
                  refine ⟨26593240688985354679688141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17728827125990236453125427 26593240688985354679688141)
                  ·
                    refine ⟨9972465258369508004883053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26593240688985354679688141 9972465258369508004883053)
                    ·
                      refine ⟨3739674471888565501831145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972465258369508004883053 3739674471888565501831145)
                      ·
                        rfl

theorem cell23_7282990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7282990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282990 prefixEnd_7282990 := by exact prefixLift 7282990
  have htrace : WordTrace (prefixWord ++ tailWord_7282990) baseStart_7282990 baseEnd_7282990 := by
    simpa [prefixWord, tailWord_7282990, baseEnd_7282990] using wordTrace_append hprefix tailTrace_7282990
  have hstable : (prefixWord ++ tailWord_7282990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282990).length < 2 ^ (prefixWord ++ tailWord_7282990).sum := by decide
  have hdescent : baseEnd_7282990 < baseStart_7282990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7282999 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_7282999 : Nat := 118140960795 + 7282999 * 2 ^ 59
def prefixEnd_7282999 : Nat := 4983230072969 + 3 ^ 40 * 7282999 * 2
def baseEnd_7282999 : Nat := 3739679093214455966618603

theorem tailTrace_7282999 : CollatzResearch.WordTrace tailWord_7282999 prefixEnd_7282999 3739679093214455966618603 := by
  unfold tailWord_7282999
  simp only [CollatzResearch.WordTrace]
  refine ⟨265632796141945935047372051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177088530761297290031581367 265632796141945935047372051)
  ·
    refine ⟨398449194212918902571058077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265632796141945935047372051 398449194212918902571058077)
    ·
      refine ⟨149418447829844588464146779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398449194212918902571058077 149418447829844588464146779)
      ·
        refine ⟨224127671744766882696220169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149418447829844588464146779 224127671744766882696220169)
        ·
          refine ⟨168095753808575162022165127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224127671744766882696220169 168095753808575162022165127)
          ·
            refine ⟨252143630712862743033247691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168095753808575162022165127 252143630712862743033247691)
            ·
              refine ⟨378215446069294114549871537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252143630712862743033247691 378215446069294114549871537)
              ·
                refine ⟨283661584551970585912403653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378215446069294114549871537 283661584551970585912403653)
                ·
                  refine ⟨53186547103494484858575685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283661584551970585912403653 53186547103494484858575685)
                  ·
                    refine ⟨9972477581905215910982941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53186547103494484858575685 9972477581905215910982941)
                    ·
                      refine ⟨3739679093214455966618603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972477581905215910982941 3739679093214455966618603)
                      ·
                        rfl

theorem cell23_7282999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_7282999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7282999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7282999 prefixEnd_7282999 := by exact prefixLift 7282999
  have htrace : WordTrace (prefixWord ++ tailWord_7282999) baseStart_7282999 baseEnd_7282999 := by
    simpa [prefixWord, tailWord_7282999, baseEnd_7282999] using wordTrace_append hprefix tailTrace_7282999
  have hstable : (prefixWord ++ tailWord_7282999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7282999).length < 2 ^ (prefixWord ++ tailWord_7282999).sum := by decide
  have hdescent : baseEnd_7282999 < baseStart_7282999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7282999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283049 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_7283049 : Nat := 118140960795 + 7283049 * 2 ^ 59
def prefixEnd_7283049 : Nat := 4983230072969 + 3 ^ 40 * 7283049 * 2
def baseEnd_7283049 : Nat := 1246568255749060256997791

theorem tailTrace_7283049 : CollatzResearch.WordTrace tailWord_7283049 prefixEnd_7283049 1246568255749060256997791 := by
  unfold tailWord_7283049
  simp only [CollatzResearch.WordTrace]
  refine ⟨265634619791764793586692201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177089746527843195724461467 265634619791764793586692201)
  ·
    refine ⟨199225964843823595190019151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265634619791764793586692201 199225964843823595190019151)
    ·
      refine ⟨298838947265735392785028727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199225964843823595190019151 298838947265735392785028727)
      ·
        refine ⟨448258420898603089177543091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298838947265735392785028727 448258420898603089177543091)
        ·
          refine ⟨672387631347904633766314637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448258420898603089177543091 672387631347904633766314637)
          ·
            refine ⟨252145361755464237662367989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672387631347904633766314637 252145361755464237662367989)
            ·
              refine ⟨23638627664574772280846999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252145361755464237662367989 23638627664574772280846999)
              ·
                refine ⟨35457941496862158421270499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23638627664574772280846999 35457941496862158421270499)
                ·
                  refine ⟨53186912245293237631905749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35457941496862158421270499 53186912245293237631905749)
                  ·
                    refine ⟨1246568255749060256997791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53186912245293237631905749 1246568255749060256997791)
                    ·
                      rfl

theorem cell23_7283049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_7283049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283049 prefixEnd_7283049 := by exact prefixLift 7283049
  have htrace : WordTrace (prefixWord ++ tailWord_7283049) baseStart_7283049 baseEnd_7283049 := by
    simpa [prefixWord, tailWord_7283049, baseEnd_7283049] using wordTrace_append hprefix tailTrace_7283049
  have hstable : (prefixWord ++ tailWord_7283049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283049).length < 2 ^ (prefixWord ++ tailWord_7283049).sum := by decide
  have hdescent : baseEnd_7283049 < baseStart_7283049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283053 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 5]
def baseStart_7283053 : Nat := 118140960795 + 7283053 * 2 ^ 59
def prefixEnd_7283053 : Nat := 4983230072969 + 3 ^ 40 * 7283053 * 2
def baseEnd_7283053 : Nat := 415522980129977639482595

theorem tailTrace_7283053 : CollatzResearch.WordTrace tailWord_7283053 prefixEnd_7283053 415522980129977639482595 := by
  unfold tailWord_7283053
  simp only [CollatzResearch.WordTrace]
  refine ⟨265634765683750302269837813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177089843789166868179891875 265634765683750302269837813)
  ·
    refine ⟨24903259282851590837797295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265634765683750302269837813 24903259282851590837797295)
    ·
      refine ⟨37354888924277386256695943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24903259282851590837797295 37354888924277386256695943)
      ·
        refine ⟨56032333386416079385043915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37354888924277386256695943 56032333386416079385043915)
        ·
          refine ⟨84048500079624119077565873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56032333386416079385043915 84048500079624119077565873)
          ·
            refine ⟨63036375059718089308174405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84048500079624119077565873 63036375059718089308174405)
            ·
              refine ⟨11819320323697141745282701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63036375059718089308174405 11819320323697141745282701)
              ·
                refine ⟨4432245121386428154481013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11819320323697141745282701 4432245121386428154481013)
                ·
                  refine ⟨415522980129977639482595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4432245121386428154481013 415522980129977639482595)
                  ·
                    rfl

theorem cell23_7283053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_7283053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283053 prefixEnd_7283053 := by exact prefixLift 7283053
  have htrace : WordTrace (prefixWord ++ tailWord_7283053) baseStart_7283053 baseEnd_7283053 := by
    simpa [prefixWord, tailWord_7283053, baseEnd_7283053] using wordTrace_append hprefix tailTrace_7283053
  have hstable : (prefixWord ++ tailWord_7283053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283053).length < 2 ^ (prefixWord ++ tailWord_7283053).sum := by decide
  have hdescent : baseEnd_7283053 < baseStart_7283053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283109 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 10]
def baseStart_7283109 : Nat := 118140960795 + 7283109 * 2 ^ 59
def prefixEnd_7283109 : Nat := 4983230072969 + 3 ^ 40 * 7283109 * 2
def baseEnd_7283109 : Nat := 415526175120716726249233

theorem tailTrace_7283109 : CollatzResearch.WordTrace tailWord_7283109 prefixEnd_7283109 415526175120716726249233 := by
  unfold tailWord_7283109
  simp only [CollatzResearch.WordTrace]
  refine ⟨265636808171547423833876381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177091205447698282555917587 265636808171547423833876381)
  ·
    refine ⟨99613803064330283937703643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265636808171547423833876381 99613803064330283937703643)
    ·
      refine ⟨149420704596495425906555465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99613803064330283937703643 149420704596495425906555465)
      ·
        refine ⟨112065528447371569429916599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149420704596495425906555465 112065528447371569429916599)
        ·
          refine ⟨168098292671057354144874899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112065528447371569429916599 168098292671057354144874899)
          ·
            refine ⟨252147439006586031217312349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168098292671057354144874899 252147439006586031217312349)
            ·
              refine ⟨94555289627469761706492131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252147439006586031217312349 94555289627469761706492131)
              ·
                refine ⟨141832934441204642559738197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94555289627469761706492131 141832934441204642559738197)
                ·
                  refine ⟨415526175120716726249233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141832934441204642559738197 415526175120716726249233)
                  ·
                    rfl

theorem cell23_7283109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_7283109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283109 prefixEnd_7283109 := by exact prefixLift 7283109
  have htrace : WordTrace (prefixWord ++ tailWord_7283109) baseStart_7283109 baseEnd_7283109 := by
    simpa [prefixWord, tailWord_7283109, baseEnd_7283109] using wordTrace_append hprefix tailTrace_7283109
  have hstable : (prefixWord ++ tailWord_7283109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283109).length < 2 ^ (prefixWord ++ tailWord_7283109).sum := by decide
  have hdescent : baseEnd_7283109 < baseStart_7283109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283139 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 9]
def baseStart_7283139 : Nat := 118140960795 + 7283139 * 2 ^ 59
def prefixEnd_7283139 : Nat := 4983230072969 + 3 ^ 40 * 7283139 * 2
def baseEnd_7283139 : Nat := 1246583660168695139622653

theorem tailTrace_7283139 : CollatzResearch.WordTrace tailWord_7283139 prefixEnd_7283139 1246583660168695139622653 := by
  unfold tailWord_7283139
  simp only [CollatzResearch.WordTrace]
  refine ⟨265637902361438738957468471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177091934907625825971645647 265637902361438738957468471)
  ·
    refine ⟨398456853542158108436202707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265637902361438738957468471 398456853542158108436202707)
    ·
      refine ⟨597685280313237162654304061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398456853542158108436202707 597685280313237162654304061)
      ·
        refine ⟨224131980117463935995364023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597685280313237162654304061 224131980117463935995364023)
        ·
          refine ⟨336197970176195903993046035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224131980117463935995364023 336197970176195903993046035)
          ·
            refine ⟨504296955264293855989569053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336197970176195903993046035 504296955264293855989569053)
            ·
              refine ⟨189111358224110195996088395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504296955264293855989569053 189111358224110195996088395)
              ·
                refine ⟨283667037336165293994132593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189111358224110195996088395 283667037336165293994132593)
                ·
                  refine ⟨212750278002123970495599445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283667037336165293994132593 212750278002123970495599445)
                  ·
                    refine ⟨1246583660168695139622653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 212750278002123970495599445 1246583660168695139622653)
                    ·
                      rfl

theorem cell23_7283139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_7283139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283139 prefixEnd_7283139 := by exact prefixLift 7283139
  have htrace : WordTrace (prefixWord ++ tailWord_7283139) baseStart_7283139 baseEnd_7283139 := by
    simpa [prefixWord, tailWord_7283139, baseEnd_7283139] using wordTrace_append hprefix tailTrace_7283139
  have hstable : (prefixWord ++ tailWord_7283139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283139).length < 2 ^ (prefixWord ++ tailWord_7283139).sum := by decide
  have hdescent : baseEnd_7283139 < baseStart_7283139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283143 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 6]
def baseStart_7283143 : Nat := 118140960795 + 7283143 * 2 ^ 59
def prefixEnd_7283143 : Nat := 4983230072969 + 3 ^ 40 * 7283143 * 2
def baseEnd_7283143 : Nat := 415528114936522600357549

theorem tailTrace_7283143 : CollatzResearch.WordTrace tailWord_7283143 prefixEnd_7283143 415528114936522600357549 := by
  unfold tailWord_7283143
  simp only [CollatzResearch.WordTrace]
  refine ⟨265638048253424247640614083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177092032168949498427076055 265638048253424247640614083)
  ·
    refine ⟨398457072380136371460921125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265638048253424247640614083 398457072380136371460921125)
    ·
      refine ⟨74710701071275569648922711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398457072380136371460921125 74710701071275569648922711)
      ·
        refine ⟨112066051606913354473384067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74710701071275569648922711 112066051606913354473384067)
        ·
          refine ⟨168099077410370031710076101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112066051606913354473384067 168099077410370031710076101)
          ·
            refine ⟨31518577014444380945639269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168099077410370031710076101 31518577014444380945639269)
            ·
              refine ⟨5909733190208321427307363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31518577014444380945639269 5909733190208321427307363)
              ·
                refine ⟨8864599785312482140961045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909733190208321427307363 8864599785312482140961045)
                ·
                  refine ⟨415528114936522600357549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8864599785312482140961045 415528114936522600357549)
                  ·
                    rfl

theorem cell23_7283143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 6].length) (baseStart_7283143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283143 prefixEnd_7283143 := by exact prefixLift 7283143
  have htrace : WordTrace (prefixWord ++ tailWord_7283143) baseStart_7283143 baseEnd_7283143 := by
    simpa [prefixWord, tailWord_7283143, baseEnd_7283143] using wordTrace_append hprefix tailTrace_7283143
  have hstable : (prefixWord ++ tailWord_7283143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283143).length < 2 ^ (prefixWord ++ tailWord_7283143).sum := by decide
  have hdescent : baseEnd_7283143 < baseStart_7283143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283153 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_7283153 : Nat := 118140960795 + 7283153 * 2 ^ 59
def prefixEnd_7283153 : Nat := 4983230072969 + 3 ^ 40 * 7283153 * 2
def baseEnd_7283153 : Nat := 3739758169235248364092895

theorem tailTrace_7283153 : CollatzResearch.WordTrace tailWord_7283153 prefixEnd_7283153 3739758169235248364092895 := by
  unfold tailWord_7283153
  simp only [CollatzResearch.WordTrace]
  refine ⟨265638412983388019348478113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177092275322258679565652075 265638412983388019348478113)
  ·
    refine ⟨199228809737541014511358585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265638412983388019348478113 199228809737541014511358585)
    ·
      refine ⟨149421607303155760883518939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199228809737541014511358585 149421607303155760883518939)
      ·
        refine ⟨224132410954733641325278409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149421607303155760883518939 224132410954733641325278409)
        ·
          refine ⟨168099308216050230993958807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224132410954733641325278409 168099308216050230993958807)
          ·
            refine ⟨252148962324075346490938211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168099308216050230993958807 252148962324075346490938211)
            ·
              refine ⟨378223443486113019736407317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252148962324075346490938211 378223443486113019736407317)
              ·
                refine ⟨17729223913411547800144093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 378223443486113019736407317 17729223913411547800144093)
                ·
                  refine ⟨6648458967529330425054035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17729223913411547800144093 6648458967529330425054035)
                  ·
                    refine ⟨9972688451293995637581053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6648458967529330425054035 9972688451293995637581053)
                    ·
                      refine ⟨3739758169235248364092895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972688451293995637581053 3739758169235248364092895)
                      ·
                        rfl

theorem cell23_7283153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_7283153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283153 prefixEnd_7283153 := by exact prefixLift 7283153
  have htrace : WordTrace (prefixWord ++ tailWord_7283153) baseStart_7283153 baseEnd_7283153 := by
    simpa [prefixWord, tailWord_7283153, baseEnd_7283153] using wordTrace_append hprefix tailTrace_7283153
  have hstable : (prefixWord ++ tailWord_7283153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283153).length < 2 ^ (prefixWord ++ tailWord_7283153).sum := by decide
  have hdescent : baseEnd_7283153 < baseStart_7283153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283196 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_7283196 : Nat := 118140960795 + 7283196 * 2 ^ 59
def prefixEnd_7283196 : Nat := 4983230072969 + 3 ^ 40 * 7283196 * 2
def baseEnd_7283196 : Nat := 3739780248903391695855197

theorem tailTrace_7283196 : CollatzResearch.WordTrace tailWord_7283196 prefixEnd_7283196 3739780248903391695855197 := by
  unfold tailWord_7283196
  simp only [CollatzResearch.WordTrace]
  refine ⟨132819990661116118846146721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177093320881488158461528961 132819990661116118846146721)
  ·
    refine ⟨99614992995837089134610041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132819990661116118846146721 99614992995837089134610041)
    ·
      refine ⟨74711244746877816850957531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99614992995837089134610041 74711244746877816850957531)
      ·
        refine ⟨112066867120316725276436297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74711244746877816850957531 112066867120316725276436297)
        ·
          refine ⟨84050150340237543957327223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112066867120316725276436297 84050150340237543957327223)
          ·
            refine ⟨126075225510356315935990835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84050150340237543957327223 126075225510356315935990835)
            ·
              refine ⟨189112838265534473903986253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126075225510356315935990835 189112838265534473903986253)
              ·
                refine ⟨70917314349575427713994845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189112838265534473903986253 70917314349575427713994845)
                ·
                  refine ⟨26593992881090785392748067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70917314349575427713994845 26593992881090785392748067)
                  ·
                    refine ⟨39890989321636178089122101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26593992881090785392748067 39890989321636178089122101)
                    ·
                      refine ⟨3739780248903391695855197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39890989321636178089122101 3739780248903391695855197)
                      ·
                        rfl

theorem cell23_7283196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_7283196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283196 prefixEnd_7283196 := by exact prefixLift 7283196
  have htrace : WordTrace (prefixWord ++ tailWord_7283196) baseStart_7283196 baseEnd_7283196 := by
    simpa [prefixWord, tailWord_7283196, baseEnd_7283196] using wordTrace_append hprefix tailTrace_7283196
  have hstable : (prefixWord ++ tailWord_7283196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283196).length < 2 ^ (prefixWord ++ tailWord_7283196).sum := by decide
  have hdescent : baseEnd_7283196 < baseStart_7283196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283203 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 2, 4]
def baseStart_7283203 : Nat := 118140960795 + 7283203 * 2 ^ 59
def prefixEnd_7283203 : Nat := 4983230072969 + 3 ^ 40 * 7283203 * 2
def baseEnd_7283203 : Nat := 1246594614422657722822555

theorem tailTrace_7283203 : CollatzResearch.WordTrace tailWord_7283203 prefixEnd_7283203 1246594614422657722822555 := by
  unfold tailWord_7283203
  simp only [CollatzResearch.WordTrace]
  refine ⟨265640236633206877887798263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177093491088804585258532175 265640236633206877887798263)
  ·
    refine ⟨398460354949810316831697395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265640236633206877887798263 398460354949810316831697395)
    ·
      refine ⟨597690532424715475247546093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398460354949810316831697395 597690532424715475247546093)
      ·
        refine ⟨224133949659268303217829785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597690532424715475247546093 224133949659268303217829785)
        ·
          refine ⟨168100462244451227413372339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224133949659268303217829785 168100462244451227413372339)
          ·
            refine ⟨252150693366676841120058509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168100462244451227413372339 252150693366676841120058509)
            ·
              refine ⟨94556510012503815420021941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252150693366676841120058509 94556510012503815420021941)
              ·
                refine ⟨8864672813672232695627057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94556510012503815420021941 8864672813672232695627057)
                ·
                  refine ⟨6648504610254174521720293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8864672813672232695627057 6648504610254174521720293)
                  ·
                    refine ⟨1246594614422657722822555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648504610254174521720293 1246594614422657722822555)
                    ·
                      rfl

theorem cell23_7283203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 4].length) (baseStart_7283203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283203 prefixEnd_7283203 := by exact prefixLift 7283203
  have htrace : WordTrace (prefixWord ++ tailWord_7283203) baseStart_7283203 baseEnd_7283203 := by
    simpa [prefixWord, tailWord_7283203, baseEnd_7283203] using wordTrace_append hprefix tailTrace_7283203
  have hstable : (prefixWord ++ tailWord_7283203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283203).length < 2 ^ (prefixWord ++ tailWord_7283203).sum := by decide
  have hdescent : baseEnd_7283203 < baseStart_7283203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283220 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7283220 : Nat := 118140960795 + 7283220 * 2 ^ 59
def prefixEnd_7283220 : Nat := 4983230072969 + 3 ^ 40 * 7283220 * 2
def baseEnd_7283220 : Nat := 1246597524146366533985029

theorem tailTrace_7283220 : CollatzResearch.WordTrace tailWord_7283220 prefixEnd_7283220 1246597524146366533985029 := by
  unfold tailWord_7283220
  simp only [CollatzResearch.WordTrace]
  refine ⟨132820428337072644895583557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177093904449430193194111409 132820428337072644895583557)
  ·
    refine ⟨24903830313201120917921917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132820428337072644895583557 24903830313201120917921917)
    ·
      refine ⟨9338936367450420344220719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24903830313201120917921917 9338936367450420344220719)
      ·
        refine ⟨14008404551175630516331079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9338936367450420344220719 14008404551175630516331079)
        ·
          refine ⟨21012606826763445774496619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14008404551175630516331079 21012606826763445774496619)
          ·
            refine ⟨31518910240145168661744929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21012606826763445774496619 31518910240145168661744929)
            ·
              refine ⟨23639182680108876496308697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31518910240145168661744929 23639182680108876496308697)
              ·
                refine ⟨17729387010081657372231523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23639182680108876496308697 17729387010081657372231523)
                ·
                  refine ⟨26594080515122486058347285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17729387010081657372231523 26594080515122486058347285)
                  ·
                    refine ⟨1246597524146366533985029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26594080515122486058347285 1246597524146366533985029)
                    ·
                      rfl

theorem cell23_7283220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7283220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283220 prefixEnd_7283220 := by exact prefixLift 7283220
  have htrace : WordTrace (prefixWord ++ tailWord_7283220) baseStart_7283220 baseEnd_7283220 := by
    simpa [prefixWord, tailWord_7283220, baseEnd_7283220] using wordTrace_append hprefix tailTrace_7283220
  have hstable : (prefixWord ++ tailWord_7283220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283220).length < 2 ^ (prefixWord ++ tailWord_7283220).sum := by decide
  have hdescent : baseEnd_7283220 < baseStart_7283220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283254 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_7283254 : Nat := 118140960795 + 7283254 * 2 ^ 59
def prefixEnd_7283254 : Nat := 4983230072969 + 3 ^ 40 * 7283254 * 2
def baseEnd_7283254 : Nat := 1246603343593784156309977

theorem tailTrace_7283254 : CollatzResearch.WordTrace tailWord_7283254 prefixEnd_7283254 1246603343593784156309977 := by
  unfold tailWord_7283254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602631047251382099869051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177094731170681409065269877 16602631047251382099869051)
  ·
    refine ⟨24903946570877073149803577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16602631047251382099869051 24903946570877073149803577)
    ·
      refine ⟨18677959928157804862352683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24903946570877073149803577 18677959928157804862352683)
      ·
        refine ⟨28016939892236707293529025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677959928157804862352683 28016939892236707293529025)
        ·
          refine ⟨21012704919177530470146769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28016939892236707293529025 21012704919177530470146769)
          ·
            refine ⟨15759528689383147852610077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21012704919177530470146769 15759528689383147852610077)
            ·
              refine ⟨5909823258518680444728779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15759528689383147852610077 5909823258518680444728779)
              ·
                refine ⟨8864734887778020667093169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909823258518680444728779 8864734887778020667093169)
                ·
                  refine ⟨6648551165833515500319877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8864734887778020667093169 6648551165833515500319877)
                  ·
                    refine ⟨1246603343593784156309977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648551165833515500319877 1246603343593784156309977)
                    ·
                      rfl

theorem cell23_7283254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_7283254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283254 prefixEnd_7283254 := by exact prefixLift 7283254
  have htrace : WordTrace (prefixWord ++ tailWord_7283254) baseStart_7283254 baseEnd_7283254 := by
    simpa [prefixWord, tailWord_7283254, baseEnd_7283254] using wordTrace_append hprefix tailTrace_7283254
  have hstable : (prefixWord ++ tailWord_7283254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283254).length < 2 ^ (prefixWord ++ tailWord_7283254).sum := by decide
  have hdescent : baseEnd_7283254 < baseStart_7283254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283260 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_7283260 : Nat := 118140960795 + 7283260 * 2 ^ 59
def prefixEnd_7283260 : Nat := 4983230072969 + 3 ^ 40 * 7283260 * 2
def baseEnd_7283260 : Nat := 3739813111665279445454903

theorem tailTrace_7283260 : CollatzResearch.WordTrace tailWord_7283260 prefixEnd_7283260 3739813111665279445454903 := by
  unfold tailWord_7283260
  simp only [CollatzResearch.WordTrace]
  refine ⟨132821157797000188311311617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177094877062666917748415489 132821157797000188311311617)
  ·
    refine ⟨99615868347750141233483713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132821157797000188311311617 99615868347750141233483713)
    ·
      refine ⟨74711901260812605925112785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99615868347750141233483713 74711901260812605925112785)
      ·
        refine ⟨56033925945609454443834589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74711901260812605925112785 56033925945609454443834589)
        ·
          refine ⟨21012722229603545416437971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56033925945609454443834589 21012722229603545416437971)
          ·
            refine ⟨31519083344405318124656957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21012722229603545416437971 31519083344405318124656957)
            ·
              refine ⟨11819656254151994296746359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31519083344405318124656957 11819656254151994296746359)
              ·
                refine ⟨17729484381227991445119539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11819656254151994296746359 17729484381227991445119539)
                ·
                  refine ⟨26594226571841987167679309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17729484381227991445119539 26594226571841987167679309)
                  ·
                    refine ⟨9972834964440745187879741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26594226571841987167679309 9972834964440745187879741)
                    ·
                      refine ⟨3739813111665279445454903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972834964440745187879741 3739813111665279445454903)
                      ·
                        rfl

theorem cell23_7283260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_7283260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283260 prefixEnd_7283260 := by exact prefixLift 7283260
  have htrace : WordTrace (prefixWord ++ tailWord_7283260) baseStart_7283260 baseEnd_7283260 := by
    simpa [prefixWord, tailWord_7283260, baseEnd_7283260] using wordTrace_append hprefix tailTrace_7283260
  have hstable : (prefixWord ++ tailWord_7283260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283260).length < 2 ^ (prefixWord ++ tailWord_7283260).sum := by decide
  have hdescent : baseEnd_7283260 < baseStart_7283260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283277 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_7283277 : Nat := 118140960795 + 7283277 * 2 ^ 59
def prefixEnd_7283277 : Nat := 4983230072969 + 3 ^ 40 * 7283277 * 2
def baseEnd_7283277 : Nat := 3739821840836405878942325

theorem tailTrace_7283277 : CollatzResearch.WordTrace tailWord_7283277 prefixEnd_7283277 3739821840836405878942325 := by
  unfold tailWord_7283277
  simp only [CollatzResearch.WordTrace]
  refine ⟨265642935634938788525992085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177095290423292525683994723 265642935634938788525992085)
  ·
    refine ⟨12452012607887755712155879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265642935634938788525992085 12452012607887755712155879)
    ·
      refine ⟨18678018911831633568233819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12452012607887755712155879 18678018911831633568233819)
      ·
        refine ⟨28017028367747450352350729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18678018911831633568233819 28017028367747450352350729)
        ·
          refine ⟨21012771275810587764263047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28017028367747450352350729 21012771275810587764263047)
          ·
            refine ⟨31519156913715881646394571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21012771275810587764263047 31519156913715881646394571)
            ·
              refine ⟨47278735370573822469591857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31519156913715881646394571 47278735370573822469591857)
              ·
                refine ⟨35459051527930366852193893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47278735370573822469591857 35459051527930366852193893)
                ·
                  refine ⟨6648572161486943784786355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35459051527930366852193893 6648572161486943784786355)
                  ·
                    refine ⟨9972858242230415677179533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6648572161486943784786355 9972858242230415677179533)
                    ·
                      refine ⟨3739821840836405878942325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972858242230415677179533 3739821840836405878942325)
                      ·
                        rfl

theorem cell23_7283277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_7283277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283277 prefixEnd_7283277 := by exact prefixLift 7283277
  have htrace : WordTrace (prefixWord ++ tailWord_7283277) baseStart_7283277 baseEnd_7283277 := by
    simpa [prefixWord, tailWord_7283277, baseEnd_7283277] using wordTrace_append hprefix tailTrace_7283277
  have hstable : (prefixWord ++ tailWord_7283277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283277).length < 2 ^ (prefixWord ++ tailWord_7283277).sum := by decide
  have hdescent : baseEnd_7283277 < baseStart_7283277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283303 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_7283303 : Nat := 118140960795 + 7283303 * 2 ^ 59
def prefixEnd_7283303 : Nat := 4983230072969 + 3 ^ 40 * 7283303 * 2
def baseEnd_7283303 : Nat := 3739835191333422777217205

theorem tailTrace_7283303 : CollatzResearch.WordTrace tailWord_7283303 prefixEnd_7283303 3739835191333422777217205 := by
  unfold tailWord_7283303
  simp only [CollatzResearch.WordTrace]
  refine ⟨265643883932844594966438563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177095922621896396644292375 265643883932844594966438563)
  ·
    refine ⟨398465825899266892449657845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265643883932844594966438563 398465825899266892449657845)
    ·
      refine ⟨37356171178056271167155423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 398465825899266892449657845 37356171178056271167155423)
      ·
        refine ⟨56034256767084406750733135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37356171178056271167155423 56034256767084406750733135)
        ·
          refine ⟨84051385150626610126099703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56034256767084406750733135 84051385150626610126099703)
          ·
            refine ⟨126077077725939915189149555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84051385150626610126099703 126077077725939915189149555)
            ·
              refine ⟨189115616588909872783724333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126077077725939915189149555 189115616588909872783724333)
              ·
                refine ⟨70918356220841202293896625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189115616588909872783724333 70918356220841202293896625)
                ·
                  refine ⟨53188767165630901720422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70918356220841202293896625 53188767165630901720422469)
                  ·
                    refine ⟨9972893843555794072579213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53188767165630901720422469 9972893843555794072579213)
                    ·
                      refine ⟨3739835191333422777217205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9972893843555794072579213 3739835191333422777217205)
                      ·
                        rfl

theorem cell23_7283303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_7283303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283303 prefixEnd_7283303 := by exact prefixLift 7283303
  have htrace : WordTrace (prefixWord ++ tailWord_7283303) baseStart_7283303 baseEnd_7283303 := by
    simpa [prefixWord, tailWord_7283303, baseEnd_7283303] using wordTrace_append hprefix tailTrace_7283303
  have hstable : (prefixWord ++ tailWord_7283303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283303).length < 2 ^ (prefixWord ++ tailWord_7283303).sum := by decide
  have hdescent : baseEnd_7283303 < baseStart_7283303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283353 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_7283353 : Nat := 118140960795 + 7283353 * 2 ^ 59
def prefixEnd_7283353 : Nat := 4983230072969 + 3 ^ 40 * 7283353 * 2
def baseEnd_7283353 : Nat := 1246620288455382527197325

theorem tailTrace_7283353 : CollatzResearch.WordTrace tailWord_7283353 prefixEnd_7283353 1246620288455382527197325 := by
  unfold tailWord_7283353
  simp only [CollatzResearch.WordTrace]
  refine ⟨265645707582663453505758713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177097138388442302337172475 265645707582663453505758713)
  ·
    refine ⟨199234280686997590129319035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265645707582663453505758713 199234280686997590129319035)
    ·
      refine ⟨298851421030496385193978553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199234280686997590129319035 298851421030496385193978553)
      ·
        refine ⟨224138565772872288895483915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298851421030496385193978553 224138565772872288895483915)
        ·
          refine ⟨336207848659308433343225873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224138565772872288895483915 336207848659308433343225873)
          ·
            refine ⟨252155886494481325007419405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336207848659308433343225873 252155886494481325007419405)
            ·
              refine ⟨94558457435430496877782277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252155886494481325007419405 94558457435430496877782277)
              ·
                refine ⟨17729710769143218164584177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94558457435430496877782277 17729710769143218164584177)
                ·
                  refine ⟨13297283076857413623438133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17729710769143218164584177 13297283076857413623438133)
                  ·
                    refine ⟨1246620288455382527197325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13297283076857413623438133 1246620288455382527197325)
                    ·
                      rfl

theorem cell23_7283353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_7283353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283353 prefixEnd_7283353 := by exact prefixLift 7283353
  have htrace : WordTrace (prefixWord ++ tailWord_7283353) baseStart_7283353 baseEnd_7283353 := by
    simpa [prefixWord, tailWord_7283353, baseEnd_7283353] using wordTrace_append hprefix tailTrace_7283353
  have hstable : (prefixWord ++ tailWord_7283353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283353).length < 2 ^ (prefixWord ++ tailWord_7283353).sum := by decide
  have hdescent : baseEnd_7283353 < baseStart_7283353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283357 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 5]
def baseStart_7283357 : Nat := 118140960795 + 7283357 * 2 ^ 59
def prefixEnd_7283357 : Nat := 4983230072969 + 3 ^ 40 * 7283357 * 2
def baseEnd_7283357 : Nat := 415540324365418396215773

theorem tailTrace_7283357 : CollatzResearch.WordTrace tailWord_7283357 prefixEnd_7283357 415540324365418396215773 := by
  unfold tailWord_7283357
  simp only [CollatzResearch.WordTrace]
  refine ⟨265645853474648962188904325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177097235649765974792602883 265645853474648962188904325)
  ·
    refine ⟨49808597526496680410419561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265645853474648962188904325 49808597526496680410419561)
    ·
      refine ⟨37356448144872510307814671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49808597526496680410419561 37356448144872510307814671)
      ·
        refine ⟨56034672217308765461722007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37356448144872510307814671 56034672217308765461722007)
        ·
          refine ⟨84052008325963148192583011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56034672217308765461722007 84052008325963148192583011)
          ·
            refine ⟨126078012488944722288874517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84052008325963148192583011 126078012488944722288874517)
            ·
              refine ⟨5909906835419283857290993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126078012488944722288874517 5909906835419283857290993)
              ·
                refine ⟨4432430126564462892968245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909906835419283857290993 4432430126564462892968245)
                ·
                  refine ⟨415540324365418396215773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4432430126564462892968245 415540324365418396215773)
                  ·
                    rfl

theorem cell23_7283357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_7283357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283357 prefixEnd_7283357 := by exact prefixLift 7283357
  have htrace : WordTrace (prefixWord ++ tailWord_7283357) baseStart_7283357 baseEnd_7283357 := by
    simpa [prefixWord, tailWord_7283357, baseEnd_7283357] using wordTrace_append hprefix tailTrace_7283357
  have hstable : (prefixWord ++ tailWord_7283357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283357).length < 2 ^ (prefixWord ++ tailWord_7283357).sum := by decide
  have hdescent : baseEnd_7283357 < baseStart_7283357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283390 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_7283390 : Nat := 118140960795 + 7283390 * 2 ^ 59
def prefixEnd_7283390 : Nat := 4983230072969 + 3 ^ 40 * 7283390 * 2
def baseEnd_7283390 : Nat := 3739879864150363936829305

theorem tailTrace_7283390 : CollatzResearch.WordTrace tailWord_7283390 prefixEnd_7283390 3739879864150363936829305 := by
  unfold tailWord_7283390
  simp only [CollatzResearch.WordTrace]
  refine ⟨33205882135441176103106953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177098038055686272549903749 33205882135441176103106953)
  ·
    refine ⟨24904411601580882077330215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33205882135441176103106953 24904411601580882077330215)
    ·
      refine ⟨37356617402371323115995323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24904411601580882077330215 37356617402371323115995323)
      ·
        refine ⟨56034926103556984673992985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37356617402371323115995323 56034926103556984673992985)
        ·
          refine ⟨42026194577667738505494739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56034926103556984673992985 42026194577667738505494739)
          ·
            refine ⟨63039291866501607758242109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42026194577667738505494739 63039291866501607758242109)
            ·
              refine ⟨23639734449938102909340791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63039291866501607758242109 23639734449938102909340791)
              ·
                refine ⟨35459601674907154364011187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23639734449938102909340791 35459601674907154364011187)
                ·
                  refine ⟨53189402512360731546016781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35459601674907154364011187 53189402512360731546016781)
                  ·
                    refine ⟨19946025942135274329756293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53189402512360731546016781 19946025942135274329756293)
                    ·
                      refine ⟨3739879864150363936829305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19946025942135274329756293 3739879864150363936829305)
                      ·
                        rfl

theorem cell23_7283390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_7283390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283390 prefixEnd_7283390 := by exact prefixLift 7283390
  have htrace : WordTrace (prefixWord ++ tailWord_7283390) baseStart_7283390 baseEnd_7283390 := by
    simpa [prefixWord, tailWord_7283390, baseEnd_7283390] using wordTrace_append hprefix tailTrace_7283390
  have hstable : (prefixWord ++ tailWord_7283390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283390).length < 2 ^ (prefixWord ++ tailWord_7283390).sum := by decide
  have hdescent : baseEnd_7283390 < baseStart_7283390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283417 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 1, 4]
def baseStart_7283417 : Nat := 118140960795 + 7283417 * 2 ^ 59
def prefixEnd_7283417 : Nat := 4983230072969 + 3 ^ 40 * 7283417 * 2
def baseEnd_7283417 : Nat := 1246631242709345110397227

theorem tailTrace_7283417 : CollatzResearch.WordTrace tailWord_7283417 prefixEnd_7283417 1246631242709345110397227 := by
  unfold tailWord_7283417
  simp only [CollatzResearch.WordTrace]
  refine ⟨265648041854431592436088505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177098694569621061624059003 265648041854431592436088505)
  ·
    refine ⟨199236031390823694327066379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265648041854431592436088505 199236031390823694327066379)
    ·
      refine ⟨298854047086235541490599569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199236031390823694327066379 298854047086235541490599569)
      ·
        refine ⟨224140535314676656117949677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298854047086235541490599569 224140535314676656117949677)
        ·
          refine ⟨84052700743003746044231129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224140535314676656117949677 84052700743003746044231129)
          ·
            refine ⟨63039525557252809533173347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84052700743003746044231129 63039525557252809533173347)
            ·
              refine ⟨94559288335879214299760021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63039525557252809533173347 94559288335879214299760021)
              ·
                refine ⟨4432466640744338170301251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94559288335879214299760021 4432466640744338170301251)
                ·
                  refine ⟨6648699961116507255451877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432466640744338170301251 6648699961116507255451877)
                  ·
                    refine ⟨1246631242709345110397227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6648699961116507255451877 1246631242709345110397227)
                    ·
                      rfl

theorem cell23_7283417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 1, 4].length) (baseStart_7283417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283417 prefixEnd_7283417 := by exact prefixLift 7283417
  have htrace : WordTrace (prefixWord ++ tailWord_7283417) baseStart_7283417 baseEnd_7283417 := by
    simpa [prefixWord, tailWord_7283417, baseEnd_7283417] using wordTrace_append hprefix tailTrace_7283417
  have hstable : (prefixWord ++ tailWord_7283417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283417).length < 2 ^ (prefixWord ++ tailWord_7283417).sum := by decide
  have hdescent : baseEnd_7283417 < baseStart_7283417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283480 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7283480 : Nat := 118140960795 + 7283480 * 2 ^ 59
def prefixEnd_7283480 : Nat := 4983230072969 + 3 ^ 40 * 7283480 * 2
def baseEnd_7283480 : Nat := 3739926077409268584703891

theorem tailTrace_7283480 : CollatzResearch.WordTrace tailWord_7283480 prefixEnd_7283480 3739926077409268584703891 := by
  unfold tailWord_7283480
  simp only [CollatzResearch.WordTrace]
  refine ⟨132825169826601677097815947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177100226435468902797087929 132825169826601677097815947)
  ·
    refine ⟨199237754739902515646723921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132825169826601677097815947 199237754739902515646723921)
    ·
      refine ⟨149428316054926886735042941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199237754739902515646723921 149428316054926886735042941)
      ·
        refine ⟨56035618520597582525641103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149428316054926886735042941 56035618520597582525641103)
        ·
          refine ⟨84053427780896373788461655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56035618520597582525641103 84053427780896373788461655)
          ·
            refine ⟨126080141671344560682692483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84053427780896373788461655 126080141671344560682692483)
            ·
              refine ⟨189120212507016841024038725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126080141671344560682692483 189120212507016841024038725)
              ·
                refine ⟨35460039845065657692007261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189120212507016841024038725 35460039845065657692007261)
                ·
                  refine ⟨13297514941899621634502723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35460039845065657692007261 13297514941899621634502723)
                  ·
                    refine ⟨19946272412849432451754085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13297514941899621634502723 19946272412849432451754085)
                    ·
                      refine ⟨3739926077409268584703891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19946272412849432451754085 3739926077409268584703891)
                      ·
                        rfl

theorem cell23_7283480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7283480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283480 prefixEnd_7283480 := by exact prefixLift 7283480
  have htrace : WordTrace (prefixWord ++ tailWord_7283480) baseStart_7283480 baseEnd_7283480 := by
    simpa [prefixWord, tailWord_7283480, baseEnd_7283480] using wordTrace_append hprefix tailTrace_7283480
  have hstable : (prefixWord ++ tailWord_7283480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283480).length < 2 ^ (prefixWord ++ tailWord_7283480).sum := by decide
  have hdescent : baseEnd_7283480 < baseStart_7283480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283537 : List Nat := [1, 2, 2, 1, 6, 2, 1, 8]
def baseStart_7283537 : Nat := 118140960795 + 7283537 * 2 ^ 59
def prefixEnd_7283537 : Nat := 4983230072969 + 3 ^ 40 * 7283537 * 2
def baseEnd_7283537 : Nat := 138516864659502772655227

theorem tailTrace_7283537 : CollatzResearch.WordTrace tailWord_7283537 prefixEnd_7283537 138516864659502772655227 := by
  unfold tailWord_7283537
  simp only [CollatzResearch.WordTrace]
  refine ⟨265652418613996852930456865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177101612409331235286971243 265652418613996852930456865)
  ·
    refine ⟨199239313960497639697842649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265652418613996852930456865 199239313960497639697842649)
    ·
      refine ⟨149429485470373229773381987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199239313960497639697842649 149429485470373229773381987)
      ·
        refine ⟨224144228205559844660072981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149429485470373229773381987 224144228205559844660072981)
        ·
          refine ⟨10506760697135617718440921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 224144228205559844660072981 10506760697135617718440921)
          ·
            refine ⟨7880070522851713288830691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10506760697135617718440921 7880070522851713288830691)
            ·
              refine ⟨11820105784277569933246037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880070522851713288830691 11820105784277569933246037)
              ·
                refine ⟨138516864659502772655227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11820105784277569933246037 138516864659502772655227)
                ·
                  rfl

theorem cell23_7283537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 8].length) (baseStart_7283537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283537 prefixEnd_7283537 := by exact prefixLift 7283537
  have htrace : WordTrace (prefixWord ++ tailWord_7283537) baseStart_7283537 baseEnd_7283537 := by
    simpa [prefixWord, tailWord_7283537, baseEnd_7283537] using wordTrace_append hprefix tailTrace_7283537
  have hstable : (prefixWord ++ tailWord_7283537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283537).length < 2 ^ (prefixWord ++ tailWord_7283537).sum := by decide
  have hdescent : baseEnd_7283537 < baseStart_7283537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283554 : List Nat := [3, 3, 2, 1, 3, 1, 3, 7]
def baseStart_7283554 : Nat := 118140960795 + 7283554 * 2 ^ 59
def prefixEnd_7283554 : Nat := 4983230072969 + 3 ^ 40 * 7283554 * 2
def baseEnd_7283554 : Nat := 138517187962137085006613

theorem tailTrace_7283554 : CollatzResearch.WordTrace tailWord_7283554 prefixEnd_7283554 138517187962137085006613 := by
  unfold tailWord_7283554
  simp only [CollatzResearch.WordTrace]
  refine ⟨66413259663733816208456429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177102025769956843222550477 66413259663733816208456429)
  ·
    refine ⟨24904972373900181078171161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66413259663733816208456429 24904972373900181078171161)
    ·
      refine ⟨18678729280425135808628371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24904972373900181078171161 18678729280425135808628371)
      ·
        refine ⟨28018093920637703712942557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18678729280425135808628371 28018093920637703712942557)
        ·
          refine ⟨10506785220239138892353459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28018093920637703712942557 10506785220239138892353459)
          ·
            refine ⟨15760177830358708338530189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10506785220239138892353459 15760177830358708338530189)
            ·
              refine ⟨5910066686384515626948821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15760177830358708338530189 5910066686384515626948821)
              ·
                refine ⟨138517187962137085006613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5910066686384515626948821 138517187962137085006613)
                ·
                  rfl

theorem cell23_7283554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_7283554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283554 prefixEnd_7283554 := by exact prefixLift 7283554
  have htrace : WordTrace (prefixWord ++ tailWord_7283554) baseStart_7283554 baseEnd_7283554 := by
    simpa [prefixWord, tailWord_7283554, baseEnd_7283554] using wordTrace_append hprefix tailTrace_7283554
  have hstable : (prefixWord ++ tailWord_7283554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283554).length < 2 ^ (prefixWord ++ tailWord_7283554).sum := by decide
  have hdescent : baseEnd_7283554 < baseStart_7283554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283600 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_7283600 : Nat := 118140960795 + 7283600 * 2 ^ 59
def prefixEnd_7283600 : Nat := 4983230072969 + 3 ^ 40 * 7283600 * 2
def baseEnd_7283600 : Nat := 3739987695087808115203339

theorem tailTrace_7283600 : CollatzResearch.WordTrace tailWord_7283600 prefixEnd_7283600 3739987695087808115203339 := by
  unfold tailWord_7283600
  simp only [CollatzResearch.WordTrace]
  refine ⟨132827358206384307345000127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177103144275179076460000169 132827358206384307345000127)
  ·
    refine ⟨199241037309576461017500191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132827358206384307345000127 199241037309576461017500191)
    ·
      refine ⟨298861555964364691526250287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199241037309576461017500191 298861555964364691526250287)
      ·
        refine ⟨448292333946547037289375431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298861555964364691526250287 448292333946547037289375431)
        ·
          refine ⟨672438500919820555934063147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448292333946547037289375431 672438500919820555934063147)
          ·
            refine ⟨1008657751379730833901094721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672438500919820555934063147 1008657751379730833901094721)
            ·
              refine ⟨756493313534798125425821041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008657751379730833901094721 756493313534798125425821041)
              ·
                refine ⟨567369985151098594069365781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756493313534798125425821041 567369985151098594069365781)
                ·
                  refine ⟨26595468053957746597001521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 567369985151098594069365781 26595468053957746597001521)
                  ·
                    refine ⟨19946601040468309947751141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26595468053957746597001521 19946601040468309947751141)
                    ·
                      refine ⟨3739987695087808115203339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19946601040468309947751141 3739987695087808115203339)
                      ·
                        rfl

theorem cell23_7283600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_7283600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283600 prefixEnd_7283600 := by exact prefixLift 7283600
  have htrace : WordTrace (prefixWord ++ tailWord_7283600) baseStart_7283600 baseEnd_7283600 := by
    simpa [prefixWord, tailWord_7283600, baseEnd_7283600] using wordTrace_append hprefix tailTrace_7283600
  have hstable : (prefixWord ++ tailWord_7283600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283600).length < 2 ^ (prefixWord ++ tailWord_7283600).sum := by decide
  have hdescent : baseEnd_7283600 < baseStart_7283600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283674 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_7283674 : Nat := 118140960795 + 7283674 * 2 ^ 59
def prefixEnd_7283674 : Nat := 4983230072969 + 3 ^ 40 * 7283674 * 2
def baseEnd_7283674 : Nat := 1246675230885413608559333

theorem tailTrace_7283674 : CollatzResearch.WordTrace tailWord_7283674 prefixEnd_7283674 1246675230885413608559333 := by
  unfold tailWord_7283674
  simp only [CollatzResearch.WordTrace]
  refine ⟨66414353853625131332048519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177104943609667016885462717 66414353853625131332048519)
  ·
    refine ⟨99621530780437696998072779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66414353853625131332048519 99621530780437696998072779)
    ·
      refine ⟨149432296170656545497109169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99621530780437696998072779 149432296170656545497109169)
      ·
        refine ⟨112074222127992409122831877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149432296170656545497109169 112074222127992409122831877)
        ·
          refine ⟨21013916648998576710530977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112074222127992409122831877 21013916648998576710530977)
          ·
            refine ⟨15760437486748932532898233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21013916648998576710530977 15760437486748932532898233)
            ·
              refine ⟨11820328115061699399673675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15760437486748932532898233 11820328115061699399673675)
              ·
                refine ⟨17730492172592549099510513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11820328115061699399673675 17730492172592549099510513)
                ·
                  refine ⟨13297869129444411824632885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17730492172592549099510513 13297869129444411824632885)
                  ·
                    refine ⟨1246675230885413608559333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13297869129444411824632885 1246675230885413608559333)
                    ·
                      rfl

theorem cell23_7283674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_7283674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283674 prefixEnd_7283674 := by exact prefixLift 7283674
  have htrace : WordTrace (prefixWord ++ tailWord_7283674) baseStart_7283674 baseEnd_7283674 := by
    simpa [prefixWord, tailWord_7283674, baseEnd_7283674] using wordTrace_append hprefix tailTrace_7283674
  have hstable : (prefixWord ++ tailWord_7283674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283674).length < 2 ^ (prefixWord ++ tailWord_7283674).sum := by decide
  have hdescent : baseEnd_7283674 < baseStart_7283674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283680 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_7283680 : Nat := 118140960795 + 7283680 * 2 ^ 59
def prefixEnd_7283680 : Nat := 4983230072969 + 3 ^ 40 * 7283680 * 2
def baseEnd_7283680 : Nat := 3740028773540167802202971

theorem tailTrace_7283680 : CollatzResearch.WordTrace tailWord_7283680 prefixEnd_7283680 3740028773540167802202971 := by
  unfold tailWord_7283680
  simp only [CollatzResearch.WordTrace]
  refine ⟨132828817126239394176456247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177105089501652525568608329 132828817126239394176456247)
  ·
    refine ⟨199243225689359091264684371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132828817126239394176456247 199243225689359091264684371)
    ·
      refine ⟨298864838534038636897026557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199243225689359091264684371 298864838534038636897026557)
      ·
        refine ⟨112074314450264488836384959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298864838534038636897026557 112074314450264488836384959)
        ·
          refine ⟨168111471675396733254577439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112074314450264488836384959 168111471675396733254577439)
          ·
            refine ⟨252167207513095099881866159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168111471675396733254577439 252167207513095099881866159)
            ·
              refine ⟨378250811269642649822799239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252167207513095099881866159 378250811269642649822799239)
              ·
                refine ⟨567376216904463974734198859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378250811269642649822799239 567376216904463974734198859)
                ·
                  refine ⟨851064325356695962101298289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567376216904463974734198859 851064325356695962101298289)
                  ·
                    refine ⟨638298244017521971575973717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 851064325356695962101298289 638298244017521971575973717)
                    ·
                      refine ⟨3740028773540167802202971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 638298244017521971575973717 3740028773540167802202971)
                      ·
                        rfl

theorem cell23_7283680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_7283680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283680 prefixEnd_7283680 := by exact prefixLift 7283680
  have htrace : WordTrace (prefixWord ++ tailWord_7283680) baseStart_7283680 baseEnd_7283680 := by
    simpa [prefixWord, tailWord_7283680, baseEnd_7283680] using wordTrace_append hprefix tailTrace_7283680
  have hstable : (prefixWord ++ tailWord_7283680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283680).length < 2 ^ (prefixWord ++ tailWord_7283680).sum := by decide
  have hdescent : baseEnd_7283680 < baseStart_7283680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283717 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 6]
def baseStart_7283717 : Nat := 118140960795 + 7283717 * 2 ^ 59
def prefixEnd_7283717 : Nat := 4983230072969 + 3 ^ 40 * 7283717 * 2
def baseEnd_7283717 : Nat := 415560863591598239715589

theorem tailTrace_7283717 : CollatzResearch.WordTrace tailWord_7283717 prefixEnd_7283717 415560863591598239715589 := by
  unfold tailWord_7283717
  simp only [CollatzResearch.WordTrace]
  refine ⟨265658983753344743672009405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177105989168896495781339603 265658983753344743672009405)
  ·
    refine ⟨99622118907504278877003527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265658983753344743672009405 99622118907504278877003527)
    ·
      refine ⟨149433178361256418315505291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99622118907504278877003527 149433178361256418315505291)
      ·
        refine ⟨224149767541884627473257937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149433178361256418315505291 224149767541884627473257937)
        ·
          refine ⟨168112325656413470604943453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224149767541884627473257937 168112325656413470604943453)
          ·
            refine ⟨63042122121155051476853795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168112325656413470604943453 63042122121155051476853795)
            ·
              refine ⟨94563183181732577215280693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63042122121155051476853795 94563183181732577215280693)
              ·
                refine ⟨8865298423287429113932565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94563183181732577215280693 8865298423287429113932565)
                ·
                  refine ⟨415560863591598239715589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8865298423287429113932565 415560863591598239715589)
                  ·
                    rfl

theorem cell23_7283717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_7283717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283717 prefixEnd_7283717 := by exact prefixLift 7283717
  have htrace : WordTrace (prefixWord ++ tailWord_7283717) baseStart_7283717 baseEnd_7283717 := by
    simpa [prefixWord, tailWord_7283717, baseEnd_7283717] using wordTrace_append hprefix tailTrace_7283717
  have hstable : (prefixWord ++ tailWord_7283717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283717).length < 2 ^ (prefixWord ++ tailWord_7283717).sum := by decide
  have hdescent : baseEnd_7283717 < baseStart_7283717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283751 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 6]
def baseStart_7283751 : Nat := 118140960795 + 7283751 * 2 ^ 59
def prefixEnd_7283751 : Nat := 4983230072969 + 3 ^ 40 * 7283751 * 2
def baseEnd_7283751 : Nat := 415562803407404113823905

theorem tailTrace_7283751 : CollatzResearch.WordTrace tailWord_7283751 prefixEnd_7283751 415562803407404113823905 := by
  unfold tailWord_7283751
  simp only [CollatzResearch.WordTrace]
  refine ⟨265660223835221567478747107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177106815890147711652498071 265660223835221567478747107)
  ·
    refine ⟨398490335752832351218120661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265660223835221567478747107 398490335752832351218120661)
    ·
      refine ⟨9339617244207008231674703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 398490335752832351218120661 9339617244207008231674703)
      ·
        refine ⟨14009425866310512347512055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339617244207008231674703 14009425866310512347512055)
        ·
          refine ⟨21014138799465768521268083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14009425866310512347512055 21014138799465768521268083)
          ·
            refine ⟨31521208199198652781902125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21014138799465768521268083 31521208199198652781902125)
            ·
              refine ⟨11820453074699494793213297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31521208199198652781902125 11820453074699494793213297)
              ·
                refine ⟨8865339806024621094909973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11820453074699494793213297 8865339806024621094909973)
                ·
                  refine ⟨415562803407404113823905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8865339806024621094909973 415562803407404113823905)
                  ·
                    rfl

theorem cell23_7283751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 6].length) (baseStart_7283751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283751 prefixEnd_7283751 := by exact prefixLift 7283751
  have htrace : WordTrace (prefixWord ++ tailWord_7283751) baseStart_7283751 baseEnd_7283751 := by
    simpa [prefixWord, tailWord_7283751, baseEnd_7283751] using wordTrace_append hprefix tailTrace_7283751
  have hstable : (prefixWord ++ tailWord_7283751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283751).length < 2 ^ (prefixWord ++ tailWord_7283751).sum := by decide
  have hdescent : baseEnd_7283751 < baseStart_7283751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283761 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_7283761 : Nat := 118140960795 + 7283761 * 2 ^ 59
def prefixEnd_7283761 : Nat := 4983230072969 + 3 ^ 40 * 7283761 * 2
def baseEnd_7283761 : Nat := 3740070365473181985290099

theorem tailTrace_7283761 : CollatzResearch.WordTrace tailWord_7283761 prefixEnd_7283761 3740070365473181985290099 := by
  unfold tailWord_7283761
  simp only [CollatzResearch.WordTrace]
  refine ⟨265660588565185339186611137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177107059043456892791074091 265660588565185339186611137)
  ·
    refine ⟨199245441423889004389958353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265660588565185339186611137 199245441423889004389958353)
    ·
      refine ⟨149434081067916753292468765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199245441423889004389958353 149434081067916753292468765)
      ·
        refine ⟨56037780400468782484675787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149434081067916753292468765 56037780400468782484675787)
        ·
          refine ⟨84056670600703173727013681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56037780400468782484675787 84056670600703173727013681)
          ·
            refine ⟨63042502950527380295260261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84056670600703173727013681 63042502950527380295260261)
            ·
              refine ⟨11820469303223883805361299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63042502950527380295260261 11820469303223883805361299)
              ·
                refine ⟨17730703954835825708041949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11820469303223883805361299 17730703954835825708041949)
                ·
                  refine ⟨6649013983063434640515731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17730703954835825708041949 6649013983063434640515731)
                  ·
                    refine ⟨9973520974595151960773597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649013983063434640515731 9973520974595151960773597)
                    ·
                      refine ⟨3740070365473181985290099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9973520974595151960773597 3740070365473181985290099)
                      ·
                        rfl

theorem cell23_7283761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_7283761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283761 prefixEnd_7283761 := by exact prefixLift 7283761
  have htrace : WordTrace (prefixWord ++ tailWord_7283761) baseStart_7283761 baseEnd_7283761 := by
    simpa [prefixWord, tailWord_7283761, baseEnd_7283761] using wordTrace_append hprefix tailTrace_7283761
  have hstable : (prefixWord ++ tailWord_7283761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283761).length < 2 ^ (prefixWord ++ tailWord_7283761).sum := by decide
  have hdescent : baseEnd_7283761 < baseStart_7283761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283784 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_7283784 : Nat := 118140960795 + 7283784 * 2 ^ 59
def prefixEnd_7283784 : Nat := 4983230072969 + 3 ^ 40 * 7283784 * 2
def baseEnd_7283784 : Nat := 3740082175528235395302493

theorem tailTrace_7283784 : CollatzResearch.WordTrace tailWord_7283784 prefixEnd_7283784 3740082175528235395302493 := by
  unfold tailWord_7283784
  simp only [CollatzResearch.WordTrace]
  refine ⟨132830713722051007057349203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177107618296068009409798937 132830713722051007057349203)
  ·
    refine ⟨199246070583076510586023805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132830713722051007057349203 199246070583076510586023805)
    ·
      refine ⟨74717276468653691469758927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199246070583076510586023805 74717276468653691469758927)
      ·
        refine ⟨112075914702980537204638391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74717276468653691469758927 112075914702980537204638391)
        ·
          refine ⟨168113872054470805806957587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112075914702980537204638391 168113872054470805806957587)
          ·
            refine ⟨252170808081706208710436381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168113872054470805806957587 252170808081706208710436381)
            ·
              refine ⟨94564053030639828266413643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252170808081706208710436381 94564053030639828266413643)
              ·
                refine ⟨141846079545959742399620465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94564053030639828266413643 141846079545959742399620465)
                ·
                  refine ⟨106384559659469806799715349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141846079545959742399620465 106384559659469806799715349)
                  ·
                    refine ⟨4986776234037647193736657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106384559659469806799715349 4986776234037647193736657)
                    ·
                      refine ⟨3740082175528235395302493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4986776234037647193736657 3740082175528235395302493)
                      ·
                        rfl

theorem cell23_7283784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_7283784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283784 prefixEnd_7283784 := by exact prefixLift 7283784
  have htrace : WordTrace (prefixWord ++ tailWord_7283784) baseStart_7283784 baseEnd_7283784 := by
    simpa [prefixWord, tailWord_7283784, baseEnd_7283784] using wordTrace_append hprefix tailTrace_7283784
  have hstable : (prefixWord ++ tailWord_7283784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283784).length < 2 ^ (prefixWord ++ tailWord_7283784).sum := by decide
  have hdescent : baseEnd_7283784 < baseStart_7283784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283805 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7283805 : Nat := 118140960795 + 7283805 * 2 ^ 59
def prefixEnd_7283805 : Nat := 4983230072969 + 3 ^ 40 * 7283805 * 2
def baseEnd_7283805 : Nat := 3740092958621979813139897

theorem tailTrace_7283805 : CollatzResearch.WordTrace tailWord_7283805 prefixEnd_7283805 3740092958621979813139897 := by
  unfold tailWord_7283805
  simp only [CollatzResearch.WordTrace]
  refine ⟨265662193377025934701212869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177108128918017289800808579 265662193377025934701212869)
  ·
    refine ⟨49811661258192362756477413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265662193377025934701212869 49811661258192362756477413)
    ·
      refine ⟨9339686485911068016839515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49811661258192362756477413 9339686485911068016839515)
      ·
        refine ⟨14009529728866602025259273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339686485911068016839515 14009529728866602025259273)
        ·
          refine ⟨10507147296649951518944455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14009529728866602025259273 10507147296649951518944455)
          ·
            refine ⟨15760720944974927278416683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507147296649951518944455 15760720944974927278416683)
            ·
              refine ⟨23641081417462390917625025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15760720944974927278416683 23641081417462390917625025)
              ·
                refine ⟨17730811063096793188218769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23641081417462390917625025 17730811063096793188218769)
                ·
                  refine ⟨13298108297322594891164077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17730811063096793188218769 13298108297322594891164077)
                  ·
                    refine ⟨4986790611495973084186529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13298108297322594891164077 4986790611495973084186529)
                    ·
                      refine ⟨3740092958621979813139897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4986790611495973084186529 3740092958621979813139897)
                      ·
                        rfl

theorem cell23_7283805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7283805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283805 prefixEnd_7283805 := by exact prefixLift 7283805
  have htrace : WordTrace (prefixWord ++ tailWord_7283805) baseStart_7283805 baseEnd_7283805 := by
    simpa [prefixWord, tailWord_7283805, baseEnd_7283805] using wordTrace_append hprefix tailTrace_7283805
  have hstable : (prefixWord ++ tailWord_7283805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283805).length < 2 ^ (prefixWord ++ tailWord_7283805).sum := by decide
  have hdescent : baseEnd_7283805 < baseStart_7283805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283868 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7283868 : Nat := 118140960795 + 7283868 * 2 ^ 59
def prefixEnd_7283868 : Nat := 4983230072969 + 3 ^ 40 * 7283868 * 2
def baseEnd_7283868 : Nat := 3740125307903213066652107

theorem tailTrace_7283868 : CollatzResearch.WordTrace tailWord_7283868 prefixEnd_7283868 3740125307903213066652107 := by
  unfold tailWord_7283868
  simp only [CollatzResearch.WordTrace]
  refine ⟨132832245587898848230378129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177109660783865130973837505 132832245587898848230378129)
  ·
    refine ⟨99624184190924136172783597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132832245587898848230378129 99624184190924136172783597)
    ·
      refine ⟨37359069071596551064793849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99624184190924136172783597 37359069071596551064793849)
      ·
        refine ⟨28019301803697413298595387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37359069071596551064793849 28019301803697413298595387)
        ·
          refine ⟨42028952705546119947893081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28019301803697413298595387 42028952705546119947893081)
          ·
            refine ⟨31521714529159589960919811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42028952705546119947893081 31521714529159589960919811)
            ·
              refine ⟨47282571793739384941379717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31521714529159589960919811 47282571793739384941379717)
              ·
                refine ⟨8865482211326134676508697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47282571793739384941379717 8865482211326134676508697)
                ·
                  refine ⟨6649111658494601007381523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8865482211326134676508697 6649111658494601007381523)
                  ·
                    refine ⟨9973667487741901511072285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649111658494601007381523 9973667487741901511072285)
                    ·
                      refine ⟨3740125307903213066652107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9973667487741901511072285 3740125307903213066652107)
                      ·
                        rfl

theorem cell23_7283868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7283868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283868 prefixEnd_7283868 := by exact prefixLift 7283868
  have htrace : WordTrace (prefixWord ++ tailWord_7283868) baseStart_7283868 baseEnd_7283868 := by
    simpa [prefixWord, tailWord_7283868, baseEnd_7283868] using wordTrace_append hprefix tailTrace_7283868
  have hstable : (prefixWord ++ tailWord_7283868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283868).length < 2 ^ (prefixWord ++ tailWord_7283868).sum := by decide
  have hdescent : baseEnd_7283868 < baseStart_7283868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283891 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 1, 4, 2]
def baseStart_7283891 : Nat := 118140960795 + 7283891 * 2 ^ 59
def prefixEnd_7283891 : Nat := 4983230072969 + 3 ^ 40 * 7283891 * 2
def baseEnd_7283891 : Nat := 3740137117958266476664501

theorem tailTrace_7283891 : CollatzResearch.WordTrace tailWord_7283891 prefixEnd_7283891 3740137117958266476664501 := by
  unfold tailWord_7283891
  simp only [CollatzResearch.WordTrace]
  refine ⟨265665330054714371388843527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177110220036476247592562351 265665330054714371388843527)
  ·
    refine ⟨398497995082071557083265291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265665330054714371388843527 398497995082071557083265291)
    ·
      refine ⟨597746992623107335624897937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398497995082071557083265291 597746992623107335624897937)
      ·
        refine ⟨448310244467330501718673453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597746992623107335624897937 448310244467330501718673453)
        ·
          refine ⟨168116341675248938144502545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448310244467330501718673453 168116341675248938144502545)
          ·
            refine ⟨126087256256436703608376909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168116341675248938144502545 126087256256436703608376909)
            ·
              refine ⟨47282721096163763853141341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126087256256436703608376909 47282721096163763853141341)
              ·
                refine ⟨17731020411061411444928003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47282721096163763853141341 17731020411061411444928003)
                ·
                  refine ⟨26596530616592117167392005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17731020411061411444928003 26596530616592117167392005)
                  ·
                    refine ⟨4986849490611021968886001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26596530616592117167392005 4986849490611021968886001)
                    ·
                      refine ⟨3740137117958266476664501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4986849490611021968886001 3740137117958266476664501)
                      ·
                        rfl

theorem cell23_7283891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4, 2].length) (baseStart_7283891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283891 prefixEnd_7283891 := by exact prefixLift 7283891
  have htrace : WordTrace (prefixWord ++ tailWord_7283891) baseStart_7283891 baseEnd_7283891 := by
    simpa [prefixWord, tailWord_7283891, baseEnd_7283891] using wordTrace_append hprefix tailTrace_7283891
  have hstable : (prefixWord ++ tailWord_7283891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283891).length < 2 ^ (prefixWord ++ tailWord_7283891).sum := by decide
  have hdescent : baseEnd_7283891 < baseStart_7283891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283906 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7283906 : Nat := 118140960795 + 7283906 * 2 ^ 59
def prefixEnd_7283906 : Nat := 4983230072969 + 3 ^ 40 * 7283906 * 2
def baseEnd_7283906 : Nat := 3740144820168083917976933

theorem tailTrace_7283906 : CollatzResearch.WordTrace tailWord_7283906 prefixEnd_7283906 3740144820168083917976933 := by
  unfold tailWord_7283906
  simp only [CollatzResearch.WordTrace]
  refine ⟨66416469287415007237659893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177110584766440019300426381 66416469287415007237659893)
  ·
    refine ⟨6226543995695156928530615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66416469287415007237659893 6226543995695156928530615)
    ·
      refine ⟨9339815993542735392795923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226543995695156928530615 9339815993542735392795923)
      ·
        refine ⟨14009723990314103089193885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339815993542735392795923 14009723990314103089193885)
        ·
          refine ⟨5253646496367788658447707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14009723990314103089193885 5253646496367788658447707)
          ·
            refine ⟨7880469744551682987671561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253646496367788658447707 7880469744551682987671561)
            ·
              refine ⟨5910352308413762240753671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7880469744551682987671561 5910352308413762240753671)
              ·
                refine ⟨8865528462620643361130507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910352308413762240753671 8865528462620643361130507)
                ·
                  refine ⟨13298292693930965041695761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865528462620643361130507 13298292693930965041695761)
                  ·
                    refine ⟨9973719520448223781271821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13298292693930965041695761 9973719520448223781271821)
                    ·
                      refine ⟨3740144820168083917976933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9973719520448223781271821 3740144820168083917976933)
                      ·
                        rfl

theorem cell23_7283906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7283906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283906 prefixEnd_7283906 := by exact prefixLift 7283906
  have htrace : WordTrace (prefixWord ++ tailWord_7283906) baseStart_7283906 baseEnd_7283906 := by
    simpa [prefixWord, tailWord_7283906, baseEnd_7283906] using wordTrace_append hprefix tailTrace_7283906
  have hstable : (prefixWord ++ tailWord_7283906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283906).length < 2 ^ (prefixWord ++ tailWord_7283906).sum := by decide
  have hdescent : baseEnd_7283906 < baseStart_7283906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283925 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7283925 : Nat := 118140960795 + 7283925 * 2 ^ 59
def prefixEnd_7283925 : Nat := 4983230072969 + 3 ^ 40 * 7283925 * 2
def baseEnd_7283925 : Nat := 3740154576300519343639345

theorem tailTrace_7283925 : CollatzResearch.WordTrace tailWord_7283925 prefixEnd_7283925 3740154576300519343639345 := by
  unfold tailWord_7283925
  simp only [CollatzResearch.WordTrace]
  refine ⟨265666570136591195195581229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177111046757727463463720819 265666570136591195195581229)
  ·
    refine ⟨99624963801221698198342961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265666570136591195195581229 99624963801221698198342961)
    ·
      refine ⟨74718722850916273648757221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99624963801221698198342961 74718722850916273648757221)
      ·
        refine ⟨14009760534546801309141979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74718722850916273648757221 14009760534546801309141979)
        ·
          refine ⟨21014640801820201963712969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14009760534546801309141979 21014640801820201963712969)
          ·
            refine ⟨15760980601365151472784727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21014640801820201963712969 15760980601365151472784727)
            ·
              refine ⟨23641470902047727209177091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15760980601365151472784727 23641470902047727209177091)
              ·
                refine ⟨35462206353071590813765637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23641470902047727209177091 35462206353071590813765637)
                ·
                  refine ⟨6649163691200923277581057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35462206353071590813765637 6649163691200923277581057)
                  ·
                    refine ⟨4986872768400692458185793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649163691200923277581057 4986872768400692458185793)
                    ·
                      refine ⟨3740154576300519343639345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4986872768400692458185793 3740154576300519343639345)
                      ·
                        rfl

theorem cell23_7283925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7283925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283925 prefixEnd_7283925 := by exact prefixLift 7283925
  have htrace : WordTrace (prefixWord ++ tailWord_7283925) baseStart_7283925 baseEnd_7283925 := by
    simpa [prefixWord, tailWord_7283925, baseEnd_7283925] using wordTrace_append hprefix tailTrace_7283925
  have hstable : (prefixWord ++ tailWord_7283925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283925).length < 2 ^ (prefixWord ++ tailWord_7283925).sum := by decide
  have hdescent : baseEnd_7283925 < baseStart_7283925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7283944 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_7283944 : Nat := 118140960795 + 7283944 * 2 ^ 59
def prefixEnd_7283944 : Nat := 4983230072969 + 3 ^ 40 * 7283944 * 2
def baseEnd_7283944 : Nat := 1246721444144318256433919

theorem tailTrace_7283944 : CollatzResearch.WordTrace tailWord_7283944 prefixEnd_7283944 1246721444144318256433919 := by
  unfold tailWord_7283944
  simp only [CollatzResearch.WordTrace]
  refine ⟨132833631561761180720261443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177111508749014907627015257 132833631561761180720261443)
  ·
    refine ⟨199250447342641771080392165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132833631561761180720261443 199250447342641771080392165)
    ·
      refine ⟨37359458876745332077573531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199250447342641771080392165 37359458876745332077573531)
      ·
        refine ⟨56039188315117998116360297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37359458876745332077573531 56039188315117998116360297)
        ·
          refine ⟨42029391236338498587270223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56039188315117998116360297 42029391236338498587270223)
          ·
            refine ⟨63044086854507747880905335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42029391236338498587270223 63044086854507747880905335)
            ·
              refine ⟨94566130281761621821358003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63044086854507747880905335 94566130281761621821358003)
              ·
                refine ⟨141849195422642432732037005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94566130281761621821358003 141849195422642432732037005)
                ·
                  refine ⟨53193448283490912274513877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141849195422642432732037005 53193448283490912274513877)
                  ·
                    refine ⟨1246721444144318256433919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53193448283490912274513877 1246721444144318256433919)
                    ·
                      rfl

theorem cell23_7283944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_7283944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7283944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7283944 prefixEnd_7283944 := by exact prefixLift 7283944
  have htrace : WordTrace (prefixWord ++ tailWord_7283944) baseStart_7283944 baseEnd_7283944 := by
    simpa [prefixWord, tailWord_7283944, baseEnd_7283944] using wordTrace_append hprefix tailTrace_7283944
  have hstable : (prefixWord ++ tailWord_7283944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7283944).length < 2 ^ (prefixWord ++ tailWord_7283944).sum := by decide
  have hdescent : baseEnd_7283944 < baseStart_7283944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7283944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284001 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_7284001 : Nat := 118140960795 + 7284001 * 2 ^ 59
def prefixEnd_7284001 : Nat := 4983230072969 + 3 ^ 40 * 7284001 * 2
def baseEnd_7284001 : Nat := 3740193600830261046288995

theorem tailTrace_7284001 : CollatzResearch.WordTrace tailWord_7284001 prefixEnd_7284001 3740193600830261046288995 := by
  unfold tailWord_7284001
  simp only [CollatzResearch.WordTrace]
  refine ⟨265669342084315860175347857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177112894722877240116898571 265669342084315860175347857)
  ·
    refine ⟨199252006563236895131510893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265669342084315860175347857 199252006563236895131510893)
    ·
      refine ⟨74719502461213835674316585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199252006563236895131510893 74719502461213835674316585)
      ·
        refine ⟨56039626845910376755737439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74719502461213835674316585 56039626845910376755737439)
        ·
          refine ⟨84059440268865565133606159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56039626845910376755737439 84059440268865565133606159)
          ·
            refine ⟨126089160403298347700409239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84059440268865565133606159 126089160403298347700409239)
            ·
              refine ⟨189133740604947521550613859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126089160403298347700409239 189133740604947521550613859)
              ·
                refine ⟨283700610907421282325920789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189133740604947521550613859 283700610907421282325920789)
                ·
                  refine ⟨13298466136285372609027537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283700610907421282325920789 13298466136285372609027537)
                  ·
                    refine ⟨9973849602214029456770653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13298466136285372609027537 9973849602214029456770653)
                    ·
                      refine ⟨3740193600830261046288995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9973849602214029456770653 3740193600830261046288995)
                      ·
                        rfl

theorem cell23_7284001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_7284001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284001 prefixEnd_7284001 := by exact prefixLift 7284001
  have htrace : WordTrace (prefixWord ++ tailWord_7284001) baseStart_7284001 baseEnd_7284001 := by
    simpa [prefixWord, tailWord_7284001, baseEnd_7284001] using wordTrace_append hprefix tailTrace_7284001
  have hstable : (prefixWord ++ tailWord_7284001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284001).length < 2 ^ (prefixWord ++ tailWord_7284001).sum := by decide
  have hdescent : baseEnd_7284001 < baseStart_7284001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284018 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_7284018 : Nat := 118140960795 + 7284018 * 2 ^ 59
def prefixEnd_7284018 : Nat := 4983230072969 + 3 ^ 40 * 7284018 * 2
def baseEnd_7284018 : Nat := 3740202330001387479776417

theorem tailTrace_7284018 : CollatzResearch.WordTrace tailWord_7284018 prefixEnd_7284018 3740202330001387479776417 := by
  unfold tailWord_7284018
  simp only [CollatzResearch.WordTrace]
  refine ⟨66417490531313568019679177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177113308083502848052477805 66417490531313568019679177)
  ·
    refine ⟨49813117898485176014759383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66417490531313568019679177 49813117898485176014759383)
    ·
      refine ⟨74719676847727764022139075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49813117898485176014759383 74719676847727764022139075)
      ·
        refine ⟨112079515271591646033208613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74719676847727764022139075 112079515271591646033208613)
        ·
          refine ⟨21014909113423433631226615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112079515271591646033208613 21014909113423433631226615)
          ·
            refine ⟨31522363670135150446839923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21014909113423433631226615 31522363670135150446839923)
            ·
              refine ⟨47283545505202725670259885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31522363670135150446839923 47283545505202725670259885)
              ·
                refine ⟨17731329564451022126347457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47283545505202725670259885 17731329564451022126347457)
                ·
                  refine ⟨13298497173338266594760593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17731329564451022126347457 13298497173338266594760593)
                  ·
                    refine ⟨9973872880003699946070445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13298497173338266594760593 9973872880003699946070445)
                    ·
                      refine ⟨3740202330001387479776417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9973872880003699946070445 3740202330001387479776417)
                      ·
                        rfl

theorem cell23_7284018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_7284018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284018 prefixEnd_7284018 := by exact prefixLift 7284018
  have htrace : WordTrace (prefixWord ++ tailWord_7284018) baseStart_7284018 baseEnd_7284018 := by
    simpa [prefixWord, tailWord_7284018, baseEnd_7284018] using wordTrace_append hprefix tailTrace_7284018
  have hstable : (prefixWord ++ tailWord_7284018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284018).length < 2 ^ (prefixWord ++ tailWord_7284018).sum := by decide
  have hdescent : baseEnd_7284018 < baseStart_7284018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284024 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_7284024 : Nat := 118140960795 + 7284024 * 2 ^ 59
def prefixEnd_7284024 : Nat := 4983230072969 + 3 ^ 40 * 7284024 * 2
def baseEnd_7284024 : Nat := 3740205410885314456301389

theorem tailTrace_7284024 : CollatzResearch.WordTrace tailWord_7284024 prefixEnd_7284024 3740205410885314456301389 := by
  unfold tailWord_7284024
  simp only [CollatzResearch.WordTrace]
  refine ⟨132835090481616267551717563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177113453975488356735623417 132835090481616267551717563)
  ·
    refine ⟨199252635722424401327576345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132835090481616267551717563 199252635722424401327576345)
    ·
      refine ⟨149439476791818300995682259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199252635722424401327576345 149439476791818300995682259)
      ·
        refine ⟨224159215187727451493523389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149439476791818300995682259 224159215187727451493523389)
        ·
          refine ⟨84059705695397794310071271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224159215187727451493523389 84059705695397794310071271)
          ·
            refine ⟨126089558543096691465106907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84059705695397794310071271 126089558543096691465106907)
            ·
              refine ⟨189134337814645037197660361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126089558543096691465106907 189134337814645037197660361)
              ·
                refine ⟨141850753360983777898245271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189134337814645037197660361 141850753360983777898245271)
                ·
                  refine ⟨212776130041475666847367907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141850753360983777898245271 212776130041475666847367907)
                  ·
                    refine ⟨319164195062213500271051861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 212776130041475666847367907 319164195062213500271051861)
                    ·
                      refine ⟨3740205410885314456301389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319164195062213500271051861 3740205410885314456301389)
                      ·
                        rfl

theorem cell23_7284024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_7284024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284024 prefixEnd_7284024 := by exact prefixLift 7284024
  have htrace : WordTrace (prefixWord ++ tailWord_7284024) baseStart_7284024 baseEnd_7284024 := by
    simpa [prefixWord, tailWord_7284024, baseEnd_7284024] using wordTrace_append hprefix tailTrace_7284024
  have hstable : (prefixWord ++ tailWord_7284024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284024).length < 2 ^ (prefixWord ++ tailWord_7284024).sum := by decide
  have hdescent : baseEnd_7284024 < baseStart_7284024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284048 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 3, 1, 3]
def baseStart_7284048 : Nat := 118140960795 + 7284048 * 2 ^ 59
def prefixEnd_7284048 : Nat := 4983230072969 + 3 ^ 40 * 7284048 * 2
def baseEnd_7284048 : Nat := 3740217734421022362401279

theorem tailTrace_7284048 : CollatzResearch.WordTrace tailWord_7284048 prefixEnd_7284048 3740217734421022362401279 := by
  unfold tailWord_7284048
  simp only [CollatzResearch.WordTrace]
  refine ⟨132835528157572793601154399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177114037543430391468205865 132835528157572793601154399)
  ·
    refine ⟨199253292236359190401731599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132835528157572793601154399 199253292236359190401731599)
    ·
      refine ⟨298879938354538785602597399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199253292236359190401731599 298879938354538785602597399)
      ·
        refine ⟨448319907531808178403896099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298879938354538785602597399 448319907531808178403896099)
        ·
          refine ⟨672479861297712267605844149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448319907531808178403896099 672479861297712267605844149)
          ·
            refine ⟨63044986996660525088047889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 672479861297712267605844149 63044986996660525088047889)
            ·
              refine ⟨47283740247495393816035917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63044986996660525088047889 47283740247495393816035917)
              ·
                refine ⟨17731402592810772681013469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47283740247495393816035917 17731402592810772681013469)
                ·
                  refine ⟨6649275972304039755380051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17731402592810772681013469 6649275972304039755380051)
                  ·
                    refine ⟨9973913958456059633070077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649275972304039755380051 9973913958456059633070077)
                    ·
                      refine ⟨3740217734421022362401279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9973913958456059633070077 3740217734421022362401279)
                      ·
                        rfl

theorem cell23_7284048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_7284048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284048 prefixEnd_7284048 := by exact prefixLift 7284048
  have htrace : WordTrace (prefixWord ++ tailWord_7284048) baseStart_7284048 baseEnd_7284048 := by
    simpa [prefixWord, tailWord_7284048, baseEnd_7284048] using wordTrace_append hprefix tailTrace_7284048
  have hstable : (prefixWord ++ tailWord_7284048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284048).length < 2 ^ (prefixWord ++ tailWord_7284048).sum := by decide
  have hdescent : baseEnd_7284048 < baseStart_7284048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284058 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2]
def baseStart_7284058 : Nat := 118140960795 + 7284058 * 2 ^ 59
def prefixEnd_7284058 : Nat := 4983230072969 + 3 ^ 40 * 7284058 * 2
def baseEnd_7284058 : Nat := 3740222869227567323276233

theorem tailTrace_7284058 : CollatzResearch.WordTrace tailWord_7284058 prefixEnd_7284058 3740222869227567323276233 := by
  unfold tailWord_7284058
  simp only [CollatzResearch.WordTrace]
  refine ⟨66417855261277339727543207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177114280696739572606781885 66417855261277339727543207)
  ·
    refine ⟨99626782891916009591314811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66417855261277339727543207 99626782891916009591314811)
    ·
      refine ⟨149440174337874014386972217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99626782891916009591314811 149440174337874014386972217)
      ·
        refine ⟨112080130753405510790229163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149440174337874014386972217 112080130753405510790229163)
        ·
          refine ⟨168120196130108266185343745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112080130753405510790229163 168120196130108266185343745)
          ·
            refine ⟨126090147097581199639007809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168120196130108266185343745 126090147097581199639007809)
            ·
              refine ⟨94567610323185899729255857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126090147097581199639007809 94567610323185899729255857)
              ·
                refine ⟨70925707742389424796941893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94567610323185899729255857 70925707742389424796941893)
                ·
                  refine ⟨13298570201698017149426605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70925707742389424796941893 13298570201698017149426605)
                  ·
                    refine ⟨4986963825636756431034977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13298570201698017149426605 4986963825636756431034977)
                    ·
                      refine ⟨3740222869227567323276233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4986963825636756431034977 3740222869227567323276233)
                      ·
                        rfl

theorem cell23_7284058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_7284058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284058 prefixEnd_7284058 := by exact prefixLift 7284058
  have htrace : WordTrace (prefixWord ++ tailWord_7284058) baseStart_7284058 baseEnd_7284058 := by
    simpa [prefixWord, tailWord_7284058, baseEnd_7284058] using wordTrace_append hprefix tailTrace_7284058
  have hstable : (prefixWord ++ tailWord_7284058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284058).length < 2 ^ (prefixWord ++ tailWord_7284058).sum := by decide
  have hdescent : baseEnd_7284058 < baseStart_7284058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284081 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_7284081 : Nat := 118140960795 + 7284081 * 2 ^ 59
def prefixEnd_7284081 : Nat := 4983230072969 + 3 ^ 40 * 7284081 * 2
def baseEnd_7284081 : Nat := 1246744893094206911096209

theorem tailTrace_7284081 : CollatzResearch.WordTrace tailWord_7284081 prefixEnd_7284081 1246744893094206911096209 := by
  unfold tailWord_7284081
  simp only [CollatzResearch.WordTrace]
  refine ⟨265672259924026033838260097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177114839949350689225506731 265672259924026033838260097)
  ·
    refine ⟨199254194943019525378695073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265672259924026033838260097 199254194943019525378695073)
    ·
      refine ⟨149440646207264644034021305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199254194943019525378695073 149440646207264644034021305)
      ·
        refine ⟨112080484655448483025515979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149440646207264644034021305 112080484655448483025515979)
        ·
          refine ⟨168120726983172724538273969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112080484655448483025515979 168120726983172724538273969)
          ·
            refine ⟨126090545237379543403705477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168120726983172724538273969 126090545237379543403705477)
            ·
              refine ⟨23641977232008664388194777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126090545237379543403705477 23641977232008664388194777)
              ·
                refine ⟨17731482924006498291146083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23641977232008664388194777 17731482924006498291146083)
                ·
                  refine ⟨26597224386009747436719125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17731482924006498291146083 26597224386009747436719125)
                  ·
                    refine ⟨1246744893094206911096209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26597224386009747436719125 1246744893094206911096209)
                    ·
                      rfl

theorem cell23_7284081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_7284081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284081 prefixEnd_7284081 := by exact prefixLift 7284081
  have htrace : WordTrace (prefixWord ++ tailWord_7284081) baseStart_7284081 baseEnd_7284081 := by
    simpa [prefixWord, tailWord_7284081, baseEnd_7284081] using wordTrace_append hprefix tailTrace_7284081
  have hstable : (prefixWord ++ tailWord_7284081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284081).length < 2 ^ (prefixWord ++ tailWord_7284081).sum := by decide
  have hdescent : baseEnd_7284081 < baseStart_7284081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284082 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_7284082 : Nat := 118140960795 + 7284082 * 2 ^ 59
def prefixEnd_7284082 : Nat := 4983230072969 + 3 ^ 40 * 7284082 * 2
def baseEnd_7284082 : Nat := 3740235192763275229376123

theorem tailTrace_7284082 : CollatzResearch.WordTrace tailWord_7284082 prefixEnd_7284082 3740235192763275229376123 := by
  unfold tailWord_7284082
  simp only [CollatzResearch.WordTrace]
  refine ⟨66418074099255602752261625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177114864264681607339364333 66418074099255602752261625)
  ·
    refine ⟨49813555574441702064196219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66418074099255602752261625 49813555574441702064196219)
    ·
      refine ⟨74720333361662553096294329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49813555574441702064196219 74720333361662553096294329)
      ·
        refine ⟨56040250021246914822220747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74720333361662553096294329 56040250021246914822220747)
        ·
          refine ⟨84060375031870372233331121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56040250021246914822220747 84060375031870372233331121)
          ·
            refine ⟨63045281273902779174998341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84060375031870372233331121 63045281273902779174998341)
            ·
              refine ⟨11820990238856771095312189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63045281273902779174998341 11820990238856771095312189)
              ·
                refine ⟨4432871339571289160742071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11820990238856771095312189 4432871339571289160742071)
                ·
                  refine ⟨6649307009356933741113107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432871339571289160742071 6649307009356933741113107)
                  ·
                    refine ⟨9973960514035400611669661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649307009356933741113107 9973960514035400611669661)
                    ·
                      refine ⟨3740235192763275229376123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9973960514035400611669661 3740235192763275229376123)
                      ·
                        rfl

theorem cell23_7284082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_7284082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284082 prefixEnd_7284082 := by exact prefixLift 7284082
  have htrace : WordTrace (prefixWord ++ tailWord_7284082) baseStart_7284082 baseEnd_7284082 := by
    simpa [prefixWord, tailWord_7284082, baseEnd_7284082] using wordTrace_append hprefix tailTrace_7284082
  have hstable : (prefixWord ++ tailWord_7284082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284082).length < 2 ^ (prefixWord ++ tailWord_7284082).sum := by decide
  have hdescent : baseEnd_7284082 < baseStart_7284082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284085 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7284085 : Nat := 118140960795 + 7284085 * 2 ^ 59
def prefixEnd_7284085 : Nat := 4983230072969 + 3 ^ 40 * 7284085 * 2
def baseEnd_7284085 : Nat := 1246745577735079572546203

theorem tailTrace_7284085 : CollatzResearch.WordTrace tailWord_7284085 prefixEnd_7284085 1246745577735079572546203 := by
  unfold tailWord_7284085
  simp only [CollatzResearch.WordTrace]
  refine ⟨265672405816011542521405709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177114937210674361680937139 265672405816011542521405709)
  ·
    refine ⟨99627152181004328445527141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265672405816011542521405709 99627152181004328445527141)
    ·
      refine ⟨18680091033938311583536339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99627152181004328445527141 18680091033938311583536339)
      ·
        refine ⟨28020136550907467375304509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18680091033938311583536339 28020136550907467375304509)
        ·
          refine ⟨10507551206590300265739191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28020136550907467375304509 10507551206590300265739191)
          ·
            refine ⟨15761326809885450398608787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507551206590300265739191 15761326809885450398608787)
            ·
              refine ⟨23641990214828175597913181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15761326809885450398608787 23641990214828175597913181)
              ·
                refine ⟨8865746330560565849217443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23641990214828175597913181 8865746330560565849217443)
                ·
                  refine ⟨13298619495840848773826165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865746330560565849217443 13298619495840848773826165)
                  ·
                    refine ⟨1246745577735079572546203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13298619495840848773826165 1246745577735079572546203)
                    ·
                      rfl

theorem cell23_7284085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7284085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284085 prefixEnd_7284085 := by exact prefixLift 7284085
  have htrace : WordTrace (prefixWord ++ tailWord_7284085) baseStart_7284085 baseEnd_7284085 := by
    simpa [prefixWord, tailWord_7284085, baseEnd_7284085] using wordTrace_append hprefix tailTrace_7284085
  have hstable : (prefixWord ++ tailWord_7284085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284085).length < 2 ^ (prefixWord ++ tailWord_7284085).sum := by decide
  have hdescent : baseEnd_7284085 < baseStart_7284085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284091 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5]
def baseStart_7284091 : Nat := 118140960795 + 7284091 * 2 ^ 59
def prefixEnd_7284091 : Nat := 4983230072969 + 3 ^ 40 * 7284091 * 2
def baseEnd_7284091 : Nat := 3740239814089165694163581

theorem tailTrace_7284091 : CollatzResearch.WordTrace tailWord_7284091 prefixEnd_7284091 3740239814089165694163581 := by
  unfold tailWord_7284091
  simp only [CollatzResearch.WordTrace]
  refine ⟨265672624653989805546124127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177115083102659870364082751 265672624653989805546124127)
  ·
    refine ⟨398508936980984708319186191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265672624653989805546124127 398508936980984708319186191)
    ·
      refine ⟨597763405471477062478779287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398508936980984708319186191 597763405471477062478779287)
      ·
        refine ⟨896645108207215593718168931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597763405471477062478779287 896645108207215593718168931)
        ·
          refine ⟨1344967662310823390577253397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896645108207215593718168931 1344967662310823390577253397)
          ·
            refine ⟨63045359170819846433308753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1344967662310823390577253397 63045359170819846433308753)
            ·
              refine ⟨47284019378114884824981565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63045359170819846433308753 47284019378114884824981565)
              ·
                refine ⟨17731507266793081809368087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47284019378114884824981565 17731507266793081809368087)
                ·
                  refine ⟨26597260900189622714052131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17731507266793081809368087 26597260900189622714052131)
                  ·
                    refine ⟨39895891350284434071078197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26597260900189622714052131 39895891350284434071078197)
                    ·
                      refine ⟨3740239814089165694163581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39895891350284434071078197 3740239814089165694163581)
                      ·
                        rfl

theorem cell23_7284091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].length) (baseStart_7284091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284091 prefixEnd_7284091 := by exact prefixLift 7284091
  have htrace : WordTrace (prefixWord ++ tailWord_7284091) baseStart_7284091 baseEnd_7284091 := by
    simpa [prefixWord, tailWord_7284091, baseEnd_7284091] using wordTrace_append hprefix tailTrace_7284091
  have hstable : (prefixWord ++ tailWord_7284091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284091).length < 2 ^ (prefixWord ++ tailWord_7284091).sum := by decide
  have hdescent : baseEnd_7284091 < baseStart_7284091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284101 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_7284101 : Nat := 118140960795 + 7284101 * 2 ^ 59
def prefixEnd_7284101 : Nat := 4983230072969 + 3 ^ 40 * 7284101 * 2
def baseEnd_7284101 : Nat := 3740244948895710655038535

theorem tailTrace_7284101 : CollatzResearch.WordTrace tailWord_7284101 prefixEnd_7284101 3740244948895710655038535 := by
  unfold tailWord_7284101
  simp only [CollatzResearch.WordTrace]
  refine ⟨265672989383953577253988157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177115326255969051502658771 265672989383953577253988157)
  ·
    refine ⟨99627371018982591470245559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265672989383953577253988157 99627371018982591470245559)
    ·
      refine ⟨149441056528473887205368339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99627371018982591470245559 149441056528473887205368339)
      ·
        refine ⟨224161584792710830808052509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149441056528473887205368339 224161584792710830808052509)
        ·
          refine ⟨84060594297266561553019691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224161584792710830808052509 84060594297266561553019691)
          ·
            refine ⟨126090891445899842329529537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84060594297266561553019691 126090891445899842329529537)
            ·
              refine ⟨94568168584424881747147153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126090891445899842329529537 94568168584424881747147153)
              ·
                refine ⟨70926126438318661310360365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94568168584424881747147153 70926126438318661310360365)
                ·
                  refine ⟨26597297414369497991385137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70926126438318661310360365 26597297414369497991385137)
                  ·
                    refine ⟨19947973060777123493538853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26597297414369497991385137 19947973060777123493538853)
                    ·
                      refine ⟨3740244948895710655038535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19947973060777123493538853 3740244948895710655038535)
                      ·
                        rfl

theorem cell23_7284101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_7284101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284101 prefixEnd_7284101 := by exact prefixLift 7284101
  have htrace : WordTrace (prefixWord ++ tailWord_7284101) baseStart_7284101 baseEnd_7284101 := by
    simpa [prefixWord, tailWord_7284101, baseEnd_7284101] using wordTrace_append hprefix tailTrace_7284101
  have hstable : (prefixWord ++ tailWord_7284101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284101).length < 2 ^ (prefixWord ++ tailWord_7284101).sum := by decide
  have hdescent : baseEnd_7284101 < baseStart_7284101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284125 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_7284125 : Nat := 118140960795 + 7284125 * 2 ^ 59
def prefixEnd_7284125 : Nat := 4983230072969 + 3 ^ 40 * 7284125 * 2
def baseEnd_7284125 : Nat := 3740257272431418561138425

theorem tailTrace_7284125 : CollatzResearch.WordTrace tailWord_7284125 prefixEnd_7284125 3740257272431418561138425 := by
  unfold tailWord_7284125
  simp only [CollatzResearch.WordTrace]
  refine ⟨265673864735866629352861829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177115909823911086235241219 265673864735866629352861829)
  ·
    refine ⟨49813849637974993003661593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265673864735866629352861829 49813849637974993003661593)
    ·
      refine ⟨37360387228481244752746195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49813849637974993003661593 37360387228481244752746195)
      ·
        refine ⟨56040580842721867129119293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37360387228481244752746195 56040580842721867129119293)
        ·
          refine ⟨21015217816020700173419735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56040580842721867129119293 21015217816020700173419735)
          ·
            refine ⟨31522826724031050260129603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21015217816020700173419735 31522826724031050260129603)
            ·
              refine ⟨47284240086046575390194405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31522826724031050260129603 47284240086046575390194405)
              ·
                refine ⟨8865795016133732885661451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47284240086046575390194405 8865795016133732885661451)
                ·
                  refine ⟨13298692524200599328492177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865795016133732885661451 13298692524200599328492177)
                  ·
                    refine ⟨9974019393150449496369133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13298692524200599328492177 9974019393150449496369133)
                    ·
                      refine ⟨3740257272431418561138425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9974019393150449496369133 3740257272431418561138425)
                      ·
                        rfl

theorem cell23_7284125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_7284125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284125 prefixEnd_7284125 := by exact prefixLift 7284125
  have htrace : WordTrace (prefixWord ++ tailWord_7284125) baseStart_7284125 baseEnd_7284125 := by
    simpa [prefixWord, tailWord_7284125, baseEnd_7284125] using wordTrace_append hprefix tailTrace_7284125
  have hstable : (prefixWord ++ tailWord_7284125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284125).length < 2 ^ (prefixWord ++ tailWord_7284125).sum := by decide
  have hdescent : baseEnd_7284125 < baseStart_7284125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284151 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_7284151 : Nat := 118140960795 + 7284151 * 2 ^ 59
def prefixEnd_7284151 : Nat := 4983230072969 + 3 ^ 40 * 7284151 * 2
def baseEnd_7284151 : Nat := 3740270622928435459413305

theorem tailTrace_7284151 : CollatzResearch.WordTrace tailWord_7284151 prefixEnd_7284151 3740270622928435459413305 := by
  unfold tailWord_7284151
  simp only [CollatzResearch.WordTrace]
  refine ⟨265674813033772435793308307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177116542022514957195538871 265674813033772435793308307)
  ·
    refine ⟨398512219550658653689962461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265674813033772435793308307 398512219550658653689962461)
    ·
      refine ⟨149442082331496995133735923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398512219550658653689962461 149442082331496995133735923)
      ·
        refine ⟨224163123497245492700603885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149442082331496995133735923 224163123497245492700603885)
        ·
          refine ⟨84061171311467059762726457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224163123497245492700603885 84061171311467059762726457)
          ·
            refine ⟨63045878483600294822044843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84061171311467059762726457 63045878483600294822044843)
            ·
              refine ⟨94568817725400442233067265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63045878483600294822044843 94568817725400442233067265)
              ·
                refine ⟨70926613294050331674800449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94568817725400442233067265 70926613294050331674800449)
                ·
                  refine ⟨53194959970537748756100337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70926613294050331674800449 53194959970537748756100337)
                  ·
                    refine ⟨39896219977903311567075253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53194959970537748756100337 39896219977903311567075253)
                    ·
                      refine ⟨3740270622928435459413305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39896219977903311567075253 3740270622928435459413305)
                      ·
                        rfl

theorem cell23_7284151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_7284151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284151 prefixEnd_7284151 := by exact prefixLift 7284151
  have htrace : WordTrace (prefixWord ++ tailWord_7284151) baseStart_7284151 baseEnd_7284151 := by
    simpa [prefixWord, tailWord_7284151, baseEnd_7284151] using wordTrace_append hprefix tailTrace_7284151
  have hstable : (prefixWord ++ tailWord_7284151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284151).length < 2 ^ (prefixWord ++ tailWord_7284151).sum := by decide
  have hdescent : baseEnd_7284151 < baseStart_7284151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284156 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7284156 : Nat := 118140960795 + 7284156 * 2 ^ 59
def prefixEnd_7284156 : Nat := 4983230072969 + 3 ^ 40 * 7284156 * 2
def baseEnd_7284156 : Nat := 3740273190331707939850783

theorem tailTrace_7284156 : CollatzResearch.WordTrace tailWord_7284156 prefixEnd_7284156 3740273190331707939850783 := by
  unfold tailWord_7284156
  simp only [CollatzResearch.WordTrace]
  refine ⟨132837497699377160823620161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177116663599169547764826881 132837497699377160823620161)
  ·
    refine ⟨99628123274532870617715121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132837497699377160823620161 99628123274532870617715121)
    ·
      refine ⟨74721092455899652963286341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99628123274532870617715121 74721092455899652963286341)
      ·
        refine ⟨14010204835481184930616189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74721092455899652963286341 14010204835481184930616189)
        ·
          refine ⟨5253826813305444348981071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14010204835481184930616189 5253826813305444348981071)
          ·
            refine ⟨7880740219958166523471607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253826813305444348981071 7880740219958166523471607)
            ·
              refine ⟨11821110329937249785207411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880740219958166523471607 11821110329937249785207411)
              ·
                refine ⟨17731665494905874677811117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11821110329937249785207411 17731665494905874677811117)
                ·
                  refine ⟨6649374560589703004179169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17731665494905874677811117 6649374560589703004179169)
                  ·
                    refine ⟨4987030920442277253134377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649374560589703004179169 4987030920442277253134377)
                    ·
                      refine ⟨3740273190331707939850783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987030920442277253134377 3740273190331707939850783)
                      ·
                        rfl

theorem cell23_7284156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7284156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284156 prefixEnd_7284156 := by exact prefixLift 7284156
  have htrace : WordTrace (prefixWord ++ tailWord_7284156) baseStart_7284156 baseEnd_7284156 := by
    simpa [prefixWord, tailWord_7284156, baseEnd_7284156] using wordTrace_append hprefix tailTrace_7284156
  have hstable : (prefixWord ++ tailWord_7284156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284156).length < 2 ^ (prefixWord ++ tailWord_7284156).sum := by decide
  have hdescent : baseEnd_7284156 < baseStart_7284156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284171 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 2, 6]
def baseStart_7284171 : Nat := 118140960795 + 7284171 * 2 ^ 59
def prefixEnd_7284171 : Nat := 4983230072969 + 3 ^ 40 * 7284171 * 2
def baseEnd_7284171 : Nat := 1246760297513841793721071

theorem tailTrace_7284171 : CollatzResearch.WordTrace tailWord_7284171 prefixEnd_7284171 1246760297513841793721071 := by
  unfold tailWord_7284171
  simp only [CollatzResearch.WordTrace]
  refine ⟨265675542493699979209036367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177117028329133319472690911 265675542493699979209036367)
  ·
    refine ⟨398513313740549968813554551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265675542493699979209036367 398513313740549968813554551)
    ·
      refine ⟨597769970610824953220331827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398513313740549968813554551 597769970610824953220331827)
      ·
        refine ⟨896654955916237429830497741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597769970610824953220331827 896654955916237429830497741)
        ·
          refine ⟨336245608468589036186436653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 896654955916237429830497741 336245608468589036186436653)
          ·
            refine ⟨126092103175720888569913745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336245608468589036186436653 126092103175720888569913745)
            ·
              refine ⟨94569077381790666427435309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126092103175720888569913745 94569077381790666427435309)
              ·
                refine ⟨35463404018171499910288241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94569077381790666427435309 35463404018171499910288241)
                ·
                  refine ⟨26597553013628624932716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35463404018171499910288241 26597553013628624932716181)
                  ·
                    refine ⟨1246760297513841793721071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26597553013628624932716181 1246760297513841793721071)
                    ·
                      rfl

theorem cell23_7284171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_7284171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284171 prefixEnd_7284171 := by exact prefixLift 7284171
  have htrace : WordTrace (prefixWord ++ tailWord_7284171) baseStart_7284171 baseEnd_7284171 := by
    simpa [prefixWord, tailWord_7284171, baseEnd_7284171] using wordTrace_append hprefix tailTrace_7284171
  have hstable : (prefixWord ++ tailWord_7284171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284171).length < 2 ^ (prefixWord ++ tailWord_7284171).sum := by decide
  have hdescent : baseEnd_7284171 < baseStart_7284171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284172 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_7284172 : Nat := 118140960795 + 7284172 * 2 ^ 59
def prefixEnd_7284172 : Nat := 4983230072969 + 3 ^ 40 * 7284172 * 2
def baseEnd_7284172 : Nat := 3740281406022179877250709

theorem tailTrace_7284172 : CollatzResearch.WordTrace tailWord_7284172 prefixEnd_7284172 3740281406022179877250709 := by
  unfold tailWord_7284172
  simp only [CollatzResearch.WordTrace]
  refine ⟨132837789483348178189911385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177117052644464237586548513 132837789483348178189911385)
  ·
    refine ⟨99628342112511133642433539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132837789483348178189911385 99628342112511133642433539)
    ·
      refine ⟨149442513168766700463650309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99628342112511133642433539 149442513168766700463650309)
      ·
        refine ⟨28020471219143756336934433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149442513168766700463650309 28020471219143756336934433)
        ·
          refine ⟨21015353414357817252700825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28020471219143756336934433 21015353414357817252700825)
          ·
            refine ⟨15761515060768362939525619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21015353414357817252700825 15761515060768362939525619)
            ·
              refine ⟨23642272591152544409288429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15761515060768362939525619 23642272591152544409288429)
              ·
                refine ⟨8865852221682204153483161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23642272591152544409288429 8865852221682204153483161)
                ·
                  refine ⟨6649389166261653115112371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8865852221682204153483161 6649389166261653115112371)
                  ·
                    refine ⟨9974083749392479672668557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649389166261653115112371 9974083749392479672668557)
                    ·
                      refine ⟨3740281406022179877250709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9974083749392479672668557 3740281406022179877250709)
                      ·
                        rfl

theorem cell23_7284172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_7284172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284172 prefixEnd_7284172 := by exact prefixLift 7284172
  have htrace : WordTrace (prefixWord ++ tailWord_7284172) baseStart_7284172 baseEnd_7284172 := by
    simpa [prefixWord, tailWord_7284172, baseEnd_7284172] using wordTrace_append hprefix tailTrace_7284172
  have hstable : (prefixWord ++ tailWord_7284172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284172).length < 2 ^ (prefixWord ++ tailWord_7284172).sum := by decide
  have hdescent : baseEnd_7284172 < baseStart_7284172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284195 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 3, 4, 2]
def baseStart_7284195 : Nat := 118140960795 + 7284195 * 2 ^ 59
def prefixEnd_7284195 : Nat := 4983230072969 + 3 ^ 40 * 7284195 * 2
def baseEnd_7284195 : Nat := 3740293216077233287263103

theorem tailTrace_7284195 : CollatzResearch.WordTrace tailWord_7284195 prefixEnd_7284195 3740293216077233287263103 := by
  unfold tailWord_7284195
  simp only [CollatzResearch.WordTrace]
  refine ⟨265676417845613031307910039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177117611897075354205273359 265676417845613031307910039)
  ·
    refine ⟨398514626768419546961865059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265676417845613031307910039 398514626768419546961865059)
    ·
      refine ⟨597771940152629320442797589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398514626768419546961865059 597771940152629320442797589)
      ·
        refine ⟨28020559694654499395756137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 597771940152629320442797589 28020559694654499395756137)
        ·
          refine ⟨21015419770990874546817103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28020559694654499395756137 21015419770990874546817103)
          ·
            refine ⟨31523129656486311820225655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21015419770990874546817103 31523129656486311820225655)
            ·
              refine ⟨47284694484729467730338483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31523129656486311820225655 47284694484729467730338483)
              ·
                refine ⟨70927041727094201595507725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47284694484729467730338483 70927041727094201595507725)
                ·
                  refine ⟨26597640647660325598315397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70927041727094201595507725 26597640647660325598315397)
                  ·
                    refine ⟨4987057621436311049684137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26597640647660325598315397 4987057621436311049684137)
                    ·
                      refine ⟨3740293216077233287263103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987057621436311049684137 3740293216077233287263103)
                      ·
                        rfl

theorem cell23_7284195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_7284195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284195 prefixEnd_7284195 := by exact prefixLift 7284195
  have htrace : WordTrace (prefixWord ++ tailWord_7284195) baseStart_7284195 baseEnd_7284195 := by
    simpa [prefixWord, tailWord_7284195, baseEnd_7284195] using wordTrace_append hprefix tailTrace_7284195
  have hstable : (prefixWord ++ tailWord_7284195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284195).length < 2 ^ (prefixWord ++ tailWord_7284195).sum := by decide
  have hdescent : baseEnd_7284195 < baseStart_7284195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284199 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7284199 : Nat := 118140960795 + 7284199 * 2 ^ 59
def prefixEnd_7284199 : Nat := 4983230072969 + 3 ^ 40 * 7284199 * 2
def baseEnd_7284199 : Nat := 3740295269999851271613085

theorem tailTrace_7284199 : CollatzResearch.WordTrace tailWord_7284199 prefixEnd_7284199 3740295269999851271613085 := by
  unfold tailWord_7284199
  simp only [CollatzResearch.WordTrace]
  refine ⟨265676563737598539991055651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177117709158399026660703767 265676563737598539991055651)
  ·
    refine ⟨398514845606397809986583477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265676563737598539991055651 398514845606397809986583477)
    ·
      refine ⟨37360766775599794686242201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 398514845606397809986583477 37360766775599794686242201)
      ·
        refine ⟨28020575081699846014681651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37360766775599794686242201 28020575081699846014681651)
        ·
          refine ⟨42030862622549769022022477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28020575081699846014681651 42030862622549769022022477)
          ·
            refine ⟨15761573483456163383258429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42030862622549769022022477 15761573483456163383258429)
            ·
              refine ⟨5910590056296061268721911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15761573483456163383258429 5910590056296061268721911)
              ·
                refine ⟨8865885084444091903082867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910590056296061268721911 8865885084444091903082867)
                ·
                  refine ⟨13298827626666137854624301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865885084444091903082867 13298827626666137854624301)
                  ·
                    refine ⟨4987060359999801695484113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13298827626666137854624301 4987060359999801695484113)
                    ·
                      refine ⟨3740295269999851271613085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987060359999801695484113 3740295269999851271613085)
                      ·
                        rfl

theorem cell23_7284199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7284199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284199 prefixEnd_7284199 := by exact prefixLift 7284199
  have htrace : WordTrace (prefixWord ++ tailWord_7284199) baseStart_7284199 baseEnd_7284199 := by
    simpa [prefixWord, tailWord_7284199, baseEnd_7284199] using wordTrace_append hprefix tailTrace_7284199
  have hstable : (prefixWord ++ tailWord_7284199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284199).length < 2 ^ (prefixWord ++ tailWord_7284199).sum := by decide
  have hdescent : baseEnd_7284199 < baseStart_7284199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284222 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_7284222 : Nat := 118140960795 + 7284222 * 2 ^ 59
def prefixEnd_7284222 : Nat := 4983230072969 + 3 ^ 40 * 7284222 * 2
def baseEnd_7284222 : Nat := 1246769026684968227208493

theorem tailTrace_7284222 : CollatzResearch.WordTrace tailWord_7284222 prefixEnd_7284222 1246769026684968227208493 := by
  unfold tailWord_7284222
  simp only [CollatzResearch.WordTrace]
  refine ⟨33209675327064401864892865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177118268411010143279428613 33209675327064401864892865)
  ·
    refine ⟨24907256495298301398669649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33209675327064401864892865 24907256495298301398669649)
    ·
      refine ⟨18680442371473726049002237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24907256495298301398669649 18680442371473726049002237)
      ·
        refine ⟨7005165889302647268375839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18680442371473726049002237 7005165889302647268375839)
        ·
          refine ⟨10507748833953970902563759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005165889302647268375839 10507748833953970902563759)
          ·
            refine ⟨15761623250930956353845639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507748833953970902563759 15761623250930956353845639)
            ·
              refine ⟨23642434876396434530768459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15761623250930956353845639 23642434876396434530768459)
              ·
                refine ⟨35463652314594651796152689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23642434876396434530768459 35463652314594651796152689)
                ·
                  refine ⟨26597739235945988847114517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35463652314594651796152689 26597739235945988847114517)
                  ·
                    refine ⟨1246769026684968227208493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26597739235945988847114517 1246769026684968227208493)
                    ·
                      rfl

theorem cell23_7284222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_7284222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284222 prefixEnd_7284222 := by exact prefixLift 7284222
  have htrace : WordTrace (prefixWord ++ tailWord_7284222) baseStart_7284222 baseEnd_7284222 := by
    simpa [prefixWord, tailWord_7284222, baseEnd_7284222] using wordTrace_append hprefix tailTrace_7284222
  have hstable : (prefixWord ++ tailWord_7284222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284222).length < 2 ^ (prefixWord ++ tailWord_7284222).sum := by decide
  have hdescent : baseEnd_7284222 < baseStart_7284222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284225 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_7284225 : Nat := 118140960795 + 7284225 * 2 ^ 59
def prefixEnd_7284225 : Nat := 4983230072969 + 3 ^ 40 * 7284225 * 2
def baseEnd_7284225 : Nat := 3740308620496868169887965

theorem tailTrace_7284225 : CollatzResearch.WordTrace tailWord_7284225 prefixEnd_7284225 3740308620496868169887965 := by
  unfold tailWord_7284225
  simp only [CollatzResearch.WordTrace]
  refine ⟨265677512035504346431502129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177118341357002897621001419 265677512035504346431502129)
  ·
    refine ⟨199258134026628259823626597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265677512035504346431502129 199258134026628259823626597)
    ·
      refine ⟨37360900129992798716929987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199258134026628259823626597 37360900129992798716929987)
      ·
        refine ⟨56041350194989198075394981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37360900129992798716929987 56041350194989198075394981)
        ·
          refine ⟨10507753161560474639136559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56041350194989198075394981 10507753161560474639136559)
          ·
            refine ⟨15761629742340711958704839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507753161560474639136559 15761629742340711958704839)
            ·
              refine ⟨23642444613511067938057259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15761629742340711958704839 23642444613511067938057259)
              ·
                refine ⟨35463666920266601907085889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23642444613511067938057259 35463666920266601907085889)
                ·
                  refine ⟨26597750190199951430314417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35463666920266601907085889 26597750190199951430314417)
                  ·
                    refine ⟨19948312642649963572735813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26597750190199951430314417 19948312642649963572735813)
                    ·
                      refine ⟨3740308620496868169887965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19948312642649963572735813 3740308620496868169887965)
                      ·
                        rfl

theorem cell23_7284225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_7284225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284225 prefixEnd_7284225 := by exact prefixLift 7284225
  have htrace : WordTrace (prefixWord ++ tailWord_7284225) baseStart_7284225 baseEnd_7284225 := by
    simpa [prefixWord, tailWord_7284225, baseEnd_7284225] using wordTrace_append hprefix tailTrace_7284225
  have hstable : (prefixWord ++ tailWord_7284225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284225).length < 2 ^ (prefixWord ++ tailWord_7284225).sum := by decide
  have hdescent : baseEnd_7284225 < baseStart_7284225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284258 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7284258 : Nat := 118140960795 + 7284258 * 2 ^ 59
def prefixEnd_7284258 : Nat := 4983230072969 + 3 ^ 40 * 7284258 * 2
def baseEnd_7284258 : Nat := 3740325565358466540775313

theorem tailTrace_7284258 : CollatzResearch.WordTrace tailWord_7284258 prefixEnd_7284258 3740325565358466540775313 := by
  unfold tailWord_7284258
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419678911096198266863357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177119143762923195378302285 66419678911096198266863357)
  ·
    refine ⟨24907379591661074350073759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66419678911096198266863357 24907379591661074350073759)
    ·
      refine ⟨37361069387491611525110639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24907379591661074350073759 37361069387491611525110639)
      ·
        refine ⟨56041604081237417287665959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37361069387491611525110639 56041604081237417287665959)
        ·
          refine ⟨84062406121856125931498939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56041604081237417287665959 84062406121856125931498939)
          ·
            refine ⟨126093609182784188897248409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84062406121856125931498939 126093609182784188897248409)
            ·
              refine ⟨94570206887088141672936307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126093609182784188897248409 94570206887088141672936307)
              ·
                refine ⟨141855310330632212509404461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94570206887088141672936307 141855310330632212509404461)
                ·
                  refine ⟨53195741373987079691026673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141855310330632212509404461 53195741373987079691026673)
                  ·
                    refine ⟨39896806030490309768270005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53195741373987079691026673 39896806030490309768270005)
                    ·
                      refine ⟨3740325565358466540775313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39896806030490309768270005 3740325565358466540775313)
                      ·
                        rfl

theorem cell23_7284258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7284258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284258 prefixEnd_7284258 := by exact prefixLift 7284258
  have htrace : WordTrace (prefixWord ++ tailWord_7284258) baseStart_7284258 baseEnd_7284258 := by
    simpa [prefixWord, tailWord_7284258, baseEnd_7284258] using wordTrace_append hprefix tailTrace_7284258
  have hstable : (prefixWord ++ tailWord_7284258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284258).length < 2 ^ (prefixWord ++ tailWord_7284258).sum := by decide
  have hdescent : baseEnd_7284258 < baseStart_7284258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284298 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_7284298 : Nat := 118140960795 + 7284298 * 2 ^ 59
def prefixEnd_7284298 : Nat := 4983230072969 + 3 ^ 40 * 7284298 * 2
def baseEnd_7284298 : Nat := 3740346104584646384275129

theorem tailTrace_7284298 : CollatzResearch.WordTrace tailWord_7284298 prefixEnd_7284298 3740346104584646384275129 := by
  unfold tailWord_7284298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66420043641059969974727387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177120116376159919932606365 66420043641059969974727387)
  ·
    refine ⟨99630065461589954962091081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66420043641059969974727387 99630065461589954962091081)
    ·
      refine ⟨74722549096192466221568311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99630065461589954962091081 74722549096192466221568311)
      ·
        refine ⟨112083823644288699332352467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74722549096192466221568311 112083823644288699332352467)
        ·
          refine ⟨168125735466433048998528701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112083823644288699332352467 168125735466433048998528701)
          ·
            refine ⟨63047150799912393374448263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168125735466433048998528701 63047150799912393374448263)
            ·
              refine ⟨94570726199868590061672395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63047150799912393374448263 94570726199868590061672395)
              ·
                refine ⟨141856089299802885092508593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94570726199868590061672395 141856089299802885092508593)
                ·
                  refine ⟨106392066974852163819381445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141856089299802885092508593 106392066974852163819381445)
                  ·
                    refine ⟨19948512557784780716134021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106392066974852163819381445 19948512557784780716134021)
                    ·
                      refine ⟨3740346104584646384275129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19948512557784780716134021 3740346104584646384275129)
                      ·
                        rfl

theorem cell23_7284298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_7284298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284298 prefixEnd_7284298 := by exact prefixLift 7284298
  have htrace : WordTrace (prefixWord ++ tailWord_7284298) baseStart_7284298 baseEnd_7284298 := by
    simpa [prefixWord, tailWord_7284298, baseEnd_7284298] using wordTrace_append hprefix tailTrace_7284298
  have hstable : (prefixWord ++ tailWord_7284298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284298).length < 2 ^ (prefixWord ++ tailWord_7284298).sum := by decide
  have hdescent : baseEnd_7284298 < baseStart_7284298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284305 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_7284305 : Nat := 118140960795 + 7284305 * 2 ^ 59
def prefixEnd_7284305 : Nat := 4983230072969 + 3 ^ 40 * 7284305 * 2
def baseEnd_7284305 : Nat := 3740349698949227856887597

theorem tailTrace_7284305 : CollatzResearch.WordTrace tailWord_7284305 prefixEnd_7284305 3740349698949227856887597 := by
  unfold tailWord_7284305
  simp only [CollatzResearch.WordTrace]
  refine ⟨265680429875214520094414369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177120286583476346729609579 265680429875214520094414369)
  ·
    refine ⟨199260322406410890070810777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265680429875214520094414369 199260322406410890070810777)
    ·
      refine ⟨149445241804808167553108083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199260322406410890070810777 149445241804808167553108083)
      ·
        refine ⟨224167862707212251329662125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149445241804808167553108083 224167862707212251329662125)
        ·
          refine ⟨84062948515204594248623297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224167862707212251329662125 84062948515204594248623297)
          ·
            refine ⟨63047211386403445686467473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84062948515204594248623297 63047211386403445686467473)
            ·
              refine ⟨47285408539802584264850605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63047211386403445686467473 47285408539802584264850605)
              ·
                refine ⟨17732028202425969099318977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47285408539802584264850605 17732028202425969099318977)
                ·
                  refine ⟨13299021151819476824489233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17732028202425969099318977 13299021151819476824489233)
                  ·
                    refine ⟨9974265863864607618366925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13299021151819476824489233 9974265863864607618366925)
                    ·
                      refine ⟨3740349698949227856887597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9974265863864607618366925 3740349698949227856887597)
                      ·
                        rfl

theorem cell23_7284305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_7284305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284305 prefixEnd_7284305 := by exact prefixLift 7284305
  have htrace : WordTrace (prefixWord ++ tailWord_7284305) baseStart_7284305 baseEnd_7284305 := by
    simpa [prefixWord, tailWord_7284305, baseEnd_7284305] using wordTrace_append hprefix tailTrace_7284305
  have hstable : (prefixWord ++ tailWord_7284305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284305).length < 2 ^ (prefixWord ++ tailWord_7284305).sum := by decide
  have hdescent : baseEnd_7284305 < baseStart_7284305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284308 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 10]
def baseStart_7284308 : Nat := 118140960795 + 7284308 * 2 ^ 59
def prefixEnd_7284308 : Nat := 4983230072969 + 3 ^ 40 * 7284308 * 2
def baseEnd_7284308 : Nat := 415594582154576816127787

theorem tailTrace_7284308 : CollatzResearch.WordTrace tailWord_7284308 prefixEnd_7284308 415594582154576816127787 := by
  unfold tailWord_7284308
  simp only [CollatzResearch.WordTrace]
  refine ⟨132840269647101825803386789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177120359529469101071182385 132840269647101825803386789)
  ·
    refine ⟨24907550558831592338135023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132840269647101825803386789 24907550558831592338135023)
    ·
      refine ⟨37361325838247388507202535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24907550558831592338135023 37361325838247388507202535)
      ·
        refine ⟨56041988757371082760803803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37361325838247388507202535 56041988757371082760803803)
        ·
          refine ⟨84062983136056624141205705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56041988757371082760803803 84062983136056624141205705)
          ·
            refine ⟨63047237352042468105904279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84062983136056624141205705 63047237352042468105904279)
            ·
              refine ⟨94570856028063702158856419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63047237352042468105904279 94570856028063702158856419)
              ·
                refine ⟨141856284042095553238284629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94570856028063702158856419 141856284042095553238284629)
                ·
                  refine ⟨415594582154576816127787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141856284042095553238284629 415594582154576816127787)
                  ·
                    rfl

theorem cell23_7284308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_7284308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284308 prefixEnd_7284308 := by exact prefixLift 7284308
  have htrace : WordTrace (prefixWord ++ tailWord_7284308) baseStart_7284308 baseEnd_7284308 := by
    simpa [prefixWord, tailWord_7284308, baseEnd_7284308] using wordTrace_append hprefix tailTrace_7284308
  have hstable : (prefixWord ++ tailWord_7284308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284308).length < 2 ^ (prefixWord ++ tailWord_7284308).sum := by decide
  have hdescent : baseEnd_7284308 < baseStart_7284308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284342 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_7284342 : Nat := 118140960795 + 7284342 * 2 ^ 59
def prefixEnd_7284342 : Nat := 4983230072969 + 3 ^ 40 * 7284342 * 2
def baseEnd_7284342 : Nat := 415596521970382690236103

theorem tailTrace_7284342 : CollatzResearch.WordTrace tailWord_7284342 prefixEnd_7284342 415596521970382690236103 := by
  unfold tailWord_7284342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605111211005029713344455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177121186250720316942340853 16605111211005029713344455)
  ·
    refine ⟨24907666816507544570016683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16605111211005029713344455 24907666816507544570016683)
    ·
      refine ⟨37361500224761316855025025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24907666816507544570016683 37361500224761316855025025)
      ·
        refine ⟨28021125168570987641268769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37361500224761316855025025 28021125168570987641268769)
        ·
          refine ⟨21015843876428240730951577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28021125168570987641268769 21015843876428240730951577)
          ·
            refine ⟨15761882907321180548213683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21015843876428240730951577 15761882907321180548213683)
            ·
              refine ⟨23642824360981770822320525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15761882907321180548213683 23642824360981770822320525)
              ·
                refine ⟨8866059135368164058370197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23642824360981770822320525 8866059135368164058370197)
                ·
                  refine ⟨415596521970382690236103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8866059135368164058370197 415596521970382690236103)
                  ·
                    rfl

theorem cell23_7284342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_7284342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284342 prefixEnd_7284342 := by exact prefixLift 7284342
  have htrace : WordTrace (prefixWord ++ tailWord_7284342) baseStart_7284342 baseEnd_7284342 := by
    simpa [prefixWord, tailWord_7284342, baseEnd_7284342] using wordTrace_append hprefix tailTrace_7284342
  have hstable : (prefixWord ++ tailWord_7284342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284342).length < 2 ^ (prefixWord ++ tailWord_7284342).sum := by decide
  have hdescent : baseEnd_7284342 < baseStart_7284342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284402 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_7284402 : Nat := 118140960795 + 7284402 * 2 ^ 59
def prefixEnd_7284402 : Nat := 4983230072969 + 3 ^ 40 * 7284402 * 2
def baseEnd_7284402 : Nat := 1246799835524237992458217

theorem tailTrace_7284402 : CollatzResearch.WordTrace tailWord_7284402 prefixEnd_7284402 1246799835524237992458217 := by
  unfold tailWord_7284402
  simp only [CollatzResearch.WordTrace]
  refine ⟨66420991938965776415173865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177122645170575403773796973 66420991938965776415173865)
  ·
    refine ⟨49815743954224332311380399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66420991938965776415173865 49815743954224332311380399)
    ·
      refine ⟨74723615931336498467070599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49815743954224332311380399 74723615931336498467070599)
      ·
        refine ⟨112085423897004747700605899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74723615931336498467070599 112085423897004747700605899)
        ·
          refine ⟨168128135845507121550908849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112085423897004747700605899 168128135845507121550908849)
          ·
            refine ⟨126096101884130341163181637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168128135845507121550908849 126096101884130341163181637)
            ·
              refine ⟨23643019103274438968096557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126096101884130341163181637 23643019103274438968096557)
              ·
                refine ⟨8866132163727914613036209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23643019103274438968096557 8866132163727914613036209)
                ·
                  refine ⟨6649599122795935959777157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866132163727914613036209 6649599122795935959777157)
                  ·
                    refine ⟨1246799835524237992458217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6649599122795935959777157 1246799835524237992458217)
                    ·
                      rfl

theorem cell23_7284402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_7284402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284402 prefixEnd_7284402 := by exact prefixLift 7284402
  have htrace : WordTrace (prefixWord ++ tailWord_7284402) baseStart_7284402 baseEnd_7284402 := by
    simpa [prefixWord, tailWord_7284402, baseEnd_7284402] using wordTrace_append hprefix tailTrace_7284402
  have hstable : (prefixWord ++ tailWord_7284402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284402).length < 2 ^ (prefixWord ++ tailWord_7284402).sum := by decide
  have hdescent : baseEnd_7284402 < baseStart_7284402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284408 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_7284408 : Nat := 118140960795 + 7284408 * 2 ^ 59
def prefixEnd_7284408 : Nat := 4983230072969 + 3 ^ 40 * 7284408 * 2
def baseEnd_7284408 : Nat := 3740402587456640953899623

theorem tailTrace_7284408 : CollatzResearch.WordTrace tailWord_7284408 prefixEnd_7284408 3740402587456640953899623 := by
  unfold tailWord_7284408
  simp only [CollatzResearch.WordTrace]
  refine ⟨132842093296920684342706939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177122791062560912456942585 132842093296920684342706939)
  ·
    refine ⟨199263139945381026514060409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132842093296920684342706939 199263139945381026514060409)
    ·
      refine ⟨149447354959035769885545307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199263139945381026514060409 149447354959035769885545307)
      ·
        refine ⟨224171032438553654828317961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149447354959035769885545307 224171032438553654828317961)
        ·
          refine ⟨168128274328915241121238471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224171032438553654828317961 168128274328915241121238471)
          ·
            refine ⟨252192411493372861681857707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168128274328915241121238471 252192411493372861681857707)
            ·
              refine ⟨378288617240059292522786561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252192411493372861681857707 378288617240059292522786561)
              ·
                refine ⟨283716462930044469392089921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378288617240059292522786561 283716462930044469392089921)
                ·
                  refine ⟨212787347197533352044067441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283716462930044469392089921 212787347197533352044067441)
                  ·
                    refine ⟨159590510398150014033050581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212787347197533352044067441 159590510398150014033050581)
                    ·
                      refine ⟨3740402587456640953899623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159590510398150014033050581 3740402587456640953899623)
                      ·
                        rfl

theorem cell23_7284408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_7284408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284408 prefixEnd_7284408 := by exact prefixLift 7284408
  have htrace : WordTrace (prefixWord ++ tailWord_7284408) baseStart_7284408 baseEnd_7284408 := by
    simpa [prefixWord, tailWord_7284408, baseEnd_7284408] using wordTrace_append hprefix tailTrace_7284408
  have hstable : (prefixWord ++ tailWord_7284408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284408).length < 2 ^ (prefixWord ++ tailWord_7284408).sum := by decide
  have hdescent : baseEnd_7284408 < baseStart_7284408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284412 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_7284412 : Nat := 118140960795 + 7284412 * 2 ^ 59
def prefixEnd_7284412 : Nat := 4983230072969 + 3 ^ 40 * 7284412 * 2
def baseEnd_7284412 : Nat := 3740404641379258938249605

theorem tailTrace_7284412 : CollatzResearch.WordTrace tailWord_7284412 prefixEnd_7284412 3740404641379258938249605 := by
  unfold tailWord_7284412
  simp only [CollatzResearch.WordTrace]
  refine ⟨132842166242913438684279745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177122888323884584912372993 132842166242913438684279745)
  ·
    refine ⟨99631624682185079013209809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132842166242913438684279745 99631624682185079013209809)
    ·
      refine ⟨74723718511638809259907357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99631624682185079013209809 74723718511638809259907357)
      ·
        refine ⟨28021394441864553472465259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74723718511638809259907357 28021394441864553472465259)
        ·
          refine ⟨42032091662796830208697889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28021394441864553472465259 42032091662796830208697889)
          ·
            refine ⟨31524068747097622656523417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42032091662796830208697889 31524068747097622656523417)
            ·
              refine ⟨23643051560323216992392563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31524068747097622656523417 23643051560323216992392563)
              ·
                refine ⟨35464577340484825488588845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23643051560323216992392563 35464577340484825488588845)
                ·
                  refine ⟨13299216502681809558220817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35464577340484825488588845 13299216502681809558220817)
                  ·
                    refine ⟨9974412377011357168665613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13299216502681809558220817 9974412377011357168665613)
                    ·
                      refine ⟨3740404641379258938249605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9974412377011357168665613 3740404641379258938249605)
                      ·
                        rfl

theorem cell23_7284412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_7284412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284412 prefixEnd_7284412 := by exact prefixLift 7284412
  have htrace : WordTrace (prefixWord ++ tailWord_7284412) baseStart_7284412 baseEnd_7284412 := by
    simpa [prefixWord, tailWord_7284412, baseEnd_7284412] using wordTrace_append hprefix tailTrace_7284412
  have hstable : (prefixWord ++ tailWord_7284412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284412).length < 2 ^ (prefixWord ++ tailWord_7284412).sum := by decide
  have hdescent : baseEnd_7284412 < baseStart_7284412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284415 : List Nat := [1, 1, 2, 2, 2, 3, 5, 7]
def baseStart_7284415 : Nat := 118140960795 + 7284415 * 2 ^ 59
def prefixEnd_7284415 : Nat := 4983230072969 + 3 ^ 40 * 7284415 * 2
def baseEnd_7284415 : Nat := 138533562289674904685633

theorem tailTrace_7284415 : CollatzResearch.WordTrace tailWord_7284415 prefixEnd_7284415 138533562289674904685633 := by
  unfold tailWord_7284415
  simp only [CollatzResearch.WordTrace]
  refine ⟨265684441904816008880918699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177122961269877339253945799 265684441904816008880918699)
  ·
    refine ⟨398526662857224013321378049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265684441904816008880918699 398526662857224013321378049)
    ·
      refine ⟨298894997142918009991033537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398526662857224013321378049 298894997142918009991033537)
      ·
        refine ⟨224171247857188507493275153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298894997142918009991033537 224171247857188507493275153)
        ·
          refine ⟨168128435892891380619956365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224171247857188507493275153 168128435892891380619956365)
          ·
            refine ⟨63048163459834267732483637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168128435892891380619956365 63048163459834267732483637)
            ·
              refine ⟨5910765324359462599920341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63048163459834267732483637 5910765324359462599920341)
              ·
                refine ⟨138533562289674904685633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5910765324359462599920341 138533562289674904685633)
                ·
                  rfl

theorem cell23_7284415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 7].length) (baseStart_7284415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284415 prefixEnd_7284415 := by exact prefixLift 7284415
  have htrace : WordTrace (prefixWord ++ tailWord_7284415) baseStart_7284415 baseEnd_7284415 := by
    simpa [prefixWord, tailWord_7284415, baseEnd_7284415] using wordTrace_append hprefix tailTrace_7284415
  have hstable : (prefixWord ++ tailWord_7284415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284415).length < 2 ^ (prefixWord ++ tailWord_7284415).sum := by decide
  have hdescent : baseEnd_7284415 < baseStart_7284415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284426 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_7284426 : Nat := 118140960795 + 7284426 * 2 ^ 59
def prefixEnd_7284426 : Nat := 4983230072969 + 3 ^ 40 * 7284426 * 2
def baseEnd_7284426 : Nat := 3740411830108421883474541

theorem tailTrace_7284426 : CollatzResearch.WordTrace tailWord_7284426 prefixEnd_7284426 3740411830108421883474541 := by
  unfold tailWord_7284426
  simp only [CollatzResearch.WordTrace]
  refine ⟨66421210776944039439892283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177123228738517438506379421 66421210776944039439892283)
  ·
    refine ⟨99631816165416059159838425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66421210776944039439892283 99631816165416059159838425)
    ·
      refine ⟨74723862124062044369878819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99631816165416059159838425 74723862124062044369878819)
      ·
        refine ⟨112085793186093066554818229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74723862124062044369878819 112085793186093066554818229)
        ·
          refine ⟨10508043111196224989514209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112085793186093066554818229 10508043111196224989514209)
          ·
            refine ⟨7881032333397168742135657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10508043111196224989514209 7881032333397168742135657)
            ·
              refine ⟨5910774250047876556601743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881032333397168742135657 5910774250047876556601743)
              ·
                refine ⟨8866161375071814834902615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910774250047876556601743 8866161375071814834902615)
                ·
                  refine ⟨13299242062607722252353923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8866161375071814834902615 13299242062607722252353923)
                  ·
                    refine ⟨19948863093911583378530885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13299242062607722252353923 19948863093911583378530885)
                    ·
                      refine ⟨3740411830108421883474541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19948863093911583378530885 3740411830108421883474541)
                      ·
                        rfl

theorem cell23_7284426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_7284426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284426 prefixEnd_7284426 := by exact prefixLift 7284426
  have htrace : WordTrace (prefixWord ++ tailWord_7284426) baseStart_7284426 baseEnd_7284426 := by
    simpa [prefixWord, tailWord_7284426, baseEnd_7284426] using wordTrace_append hprefix tailTrace_7284426
  have hstable : (prefixWord ++ tailWord_7284426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284426).length < 2 ^ (prefixWord ++ tailWord_7284426).sum := by decide
  have hdescent : baseEnd_7284426 < baseStart_7284426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284436 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_7284436 : Nat := 118140960795 + 7284436 * 2 ^ 59
def prefixEnd_7284436 : Nat := 4983230072969 + 3 ^ 40 * 7284436 * 2
def baseEnd_7284436 : Nat := 1246805654971655614783165

theorem tailTrace_7284436 : CollatzResearch.WordTrace tailWord_7284436 prefixEnd_7284436 1246805654971655614783165 := by
  unfold tailWord_7284436
  simp only [CollatzResearch.WordTrace]
  refine ⟨132842603918869964733716581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177123471891826619644955441 132842603918869964733716581)
  ·
    refine ⟨24907988234788118387571859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132842603918869964733716581 24907988234788118387571859)
    ·
      refine ⟨37361982352182177581357789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24907988234788118387571859 37361982352182177581357789)
      ·
        refine ⟨14010743382068316593009171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37361982352182177581357789 14010743382068316593009171)
        ·
          refine ⟨21016115073102474889513757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14010743382068316593009171 21016115073102474889513757)
          ·
            refine ⟨7881043152413428083567659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21016115073102474889513757 7881043152413428083567659)
            ·
              refine ⟨11821564728620142125351489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881043152413428083567659 11821564728620142125351489)
              ·
                refine ⟨8866173546465106594013617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11821564728620142125351489 8866173546465106594013617)
                ·
                  refine ⟨6649630159848829945510213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866173546465106594013617 6649630159848829945510213)
                  ·
                    refine ⟨1246805654971655614783165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6649630159848829945510213 1246805654971655614783165)
                    ·
                      rfl

theorem cell23_7284436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_7284436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284436 prefixEnd_7284436 := by exact prefixLift 7284436
  have htrace : WordTrace (prefixWord ++ tailWord_7284436) baseStart_7284436 baseEnd_7284436 := by
    simpa [prefixWord, tailWord_7284436, baseEnd_7284436] using wordTrace_append hprefix tailTrace_7284436
  have hstable : (prefixWord ++ tailWord_7284436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284436).length < 2 ^ (prefixWord ++ tailWord_7284436).sum := by decide
  have hdescent : baseEnd_7284436 < baseStart_7284436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284485 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_7284485 : Nat := 118140960795 + 7284485 * 2 ^ 59
def prefixEnd_7284485 : Nat := 4983230072969 + 3 ^ 40 * 7284485 * 2
def baseEnd_7284485 : Nat := 3740442125467037152636769

theorem tailTrace_7284485 : CollatzResearch.WordTrace tailWord_7284485 prefixEnd_7284485 3740442125467037152636769 := by
  unfold tailWord_7284485
  simp only [CollatzResearch.WordTrace]
  refine ⟨265686995014562410835966909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177124663343041607223977939 265686995014562410835966909)
  ·
    refine ⟨99632623130460904063487591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265686995014562410835966909 99632623130460904063487591)
    ·
      refine ⟨149448934695691356095231387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99632623130460904063487591 149448934695691356095231387)
      ·
        refine ⟨224173402043537034142847081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149448934695691356095231387 224173402043537034142847081)
        ·
          refine ⟨168130051532652775607135311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224173402043537034142847081 168130051532652775607135311)
          ·
            refine ⟨252195077298979163410702967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168130051532652775607135311 252195077298979163410702967)
            ·
              refine ⟨378292615948468745116054451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252195077298979163410702967 378292615948468745116054451)
              ·
                refine ⟨567438923922703117674081677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378292615948468745116054451 567438923922703117674081677)
                ·
                  refine ⟨212789596471013669127780629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567438923922703117674081677 212789596471013669127780629)
                  ·
                    refine ⟨9974512334578765740364717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212789596471013669127780629 9974512334578765740364717)
                    ·
                      refine ⟨3740442125467037152636769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9974512334578765740364717 3740442125467037152636769)
                      ·
                        rfl

theorem cell23_7284485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_7284485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284485 prefixEnd_7284485 := by exact prefixLift 7284485
  have htrace : WordTrace (prefixWord ++ tailWord_7284485) baseStart_7284485 baseEnd_7284485 := by
    simpa [prefixWord, tailWord_7284485, baseEnd_7284485] using wordTrace_append hprefix tailTrace_7284485
  have hstable : (prefixWord ++ tailWord_7284485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284485).length < 2 ^ (prefixWord ++ tailWord_7284485).sum := by decide
  have hdescent : baseEnd_7284485 < baseStart_7284485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284495 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_7284495 : Nat := 118140960795 + 7284495 * 2 ^ 59
def prefixEnd_7284495 : Nat := 4983230072969 + 3 ^ 40 * 7284495 * 2
def baseEnd_7284495 : Nat := 3740447260273582113511723

theorem tailTrace_7284495 : CollatzResearch.WordTrace tailWord_7284495 prefixEnd_7284495 3740447260273582113511723 := by
  unfold tailWord_7284495
  simp only [CollatzResearch.WordTrace]
  refine ⟨265687359744526182543830939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177124906496350788362553959 265687359744526182543830939)
  ·
    refine ⟨398531039616789273815746409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265687359744526182543830939 398531039616789273815746409)
    ·
      refine ⟨298898279712591955361809807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398531039616789273815746409 298898279712591955361809807)
      ·
        refine ⟨448347419568887933042714711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298898279712591955361809807 448347419568887933042714711)
        ·
          refine ⟨672521129353331899564072067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448347419568887933042714711 672521129353331899564072067)
          ·
            refine ⟨1008781694029997849346108101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672521129353331899564072067 1008781694029997849346108101)
            ·
              refine ⟨189146567630624596752395269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1008781694029997849346108101 189146567630624596752395269)
              ·
                refine ⟨35464981430742111891074113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189146567630624596752395269 35464981430742111891074113)
                ·
                  refine ⟨26598736073056583918305585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35464981430742111891074113 26598736073056583918305585)
                  ·
                    refine ⟨19949052054792437938729189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26598736073056583918305585 19949052054792437938729189)
                    ·
                      refine ⟨3740447260273582113511723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19949052054792437938729189 3740447260273582113511723)
                      ·
                        rfl

theorem cell23_7284495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_7284495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284495 prefixEnd_7284495 := by exact prefixLift 7284495
  have htrace : WordTrace (prefixWord ++ tailWord_7284495) baseStart_7284495 baseEnd_7284495 := by
    simpa [prefixWord, tailWord_7284495, baseEnd_7284495] using wordTrace_append hprefix tailTrace_7284495
  have hstable : (prefixWord ++ tailWord_7284495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284495).length < 2 ^ (prefixWord ++ tailWord_7284495).sum := by decide
  have hdescent : baseEnd_7284495 < baseStart_7284495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284510 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7284510 : Nat := 118140960795 + 7284510 * 2 ^ 59
def prefixEnd_7284510 : Nat := 4983230072969 + 3 ^ 40 * 7284510 * 2
def baseEnd_7284510 : Nat := 3740454962483399554824155

theorem tailTrace_7284510 : CollatzResearch.WordTrace tailWord_7284510 prefixEnd_7284510 3740454962483399554824155 := by
  unfold tailWord_7284510
  simp only [CollatzResearch.WordTrace]
  refine ⟨33210988354933980013203373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177125271226314560070417989 33210988354933980013203373)
  ·
    refine ⟨12454120633100242504951265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33210988354933980013203373 12454120633100242504951265)
    ·
      refine ⟨9340590474825181878713449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12454120633100242504951265 9340590474825181878713449)
      ·
        refine ⟨7005442856118886409035087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9340590474825181878713449 7005442856118886409035087)
        ·
          refine ⟨10508164284178329613552631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005442856118886409035087 10508164284178329613552631)
          ·
            refine ⟨15762246426267494420328947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10508164284178329613552631 15762246426267494420328947)
            ·
              refine ⟨23643369639401241630493421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15762246426267494420328947 23643369639401241630493421)
              ·
                refine ⟨8866263614775465611435033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23643369639401241630493421 8866263614775465611435033)
                ·
                  refine ⟨6649697711081599208576275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866263614775465611435033 6649697711081599208576275)
                  ·
                    refine ⟨9974546566622398812864413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649697711081599208576275 9974546566622398812864413)
                    ·
                      refine ⟨3740454962483399554824155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9974546566622398812864413 3740454962483399554824155)
                      ·
                        rfl

theorem cell23_7284510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7284510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284510 prefixEnd_7284510 := by exact prefixLift 7284510
  have htrace : WordTrace (prefixWord ++ tailWord_7284510) baseStart_7284510 baseEnd_7284510 := by
    simpa [prefixWord, tailWord_7284510, baseEnd_7284510] using wordTrace_append hprefix tailTrace_7284510
  have hstable : (prefixWord ++ tailWord_7284510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284510).length < 2 ^ (prefixWord ++ tailWord_7284510).sum := by decide
  have hdescent : baseEnd_7284510 < baseStart_7284510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284550 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7284550 : Nat := 118140960795 + 7284550 * 2 ^ 59
def prefixEnd_7284550 : Nat := 4983230072969 + 3 ^ 40 * 7284550 * 2
def baseEnd_7284550 : Nat := 3740475501709579398323971

theorem tailTrace_7284550 : CollatzResearch.WordTrace tailWord_7284550 prefixEnd_7284550 3740475501709579398323971 := by
  unfold tailWord_7284550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302792679978966466783847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 177126243839551284624722069 8302792679978966466783847)
  ·
    refine ⟨12454189019968449700175771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8302792679978966466783847 12454189019968449700175771)
    ·
      refine ⟨18681283529952674550263657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12454189019968449700175771 18681283529952674550263657)
      ·
        refine ⟨14010962647464505912697743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18681283529952674550263657 14010962647464505912697743)
        ·
          refine ⟨21016443971196758869046615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14010962647464505912697743 21016443971196758869046615)
          ·
            refine ⟨31524665956795138303569923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21016443971196758869046615 31524665956795138303569923)
            ·
              refine ⟨47286998935192707455354885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31524665956795138303569923 47286998935192707455354885)
              ·
                refine ⟨8866312300348632647879041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47286998935192707455354885 8866312300348632647879041)
                ·
                  refine ⟨6649734225261474485909281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866312300348632647879041 6649734225261474485909281)
                  ·
                    refine ⟨4987300668946105864431961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649734225261474485909281 4987300668946105864431961)
                    ·
                      refine ⟨3740475501709579398323971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987300668946105864431961 3740475501709579398323971)
                      ·
                        rfl

theorem cell23_7284550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7284550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284550 prefixEnd_7284550 := by exact prefixLift 7284550
  have htrace : WordTrace (prefixWord ++ tailWord_7284550) baseStart_7284550 baseEnd_7284550 := by
    simpa [prefixWord, tailWord_7284550, baseEnd_7284550] using wordTrace_append hprefix tailTrace_7284550
  have hstable : (prefixWord ++ tailWord_7284550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284550).length < 2 ^ (prefixWord ++ tailWord_7284550).sum := by decide
  have hdescent : baseEnd_7284550 < baseStart_7284550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284552 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_7284552 : Nat := 118140960795 + 7284552 * 2 ^ 59
def prefixEnd_7284552 : Nat := 4983230072969 + 3 ^ 40 * 7284552 * 2
def baseEnd_7284552 : Nat := 1246825509556962796832987

theorem tailTrace_7284552 : CollatzResearch.WordTrace tailWord_7284552 prefixEnd_7284552 1246825509556962796832987 := by
  unfold tailWord_7284552
  simp only [CollatzResearch.WordTrace]
  refine ⟨132844719352659840639327955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177126292470213120852437273 132844719352659840639327955)
  ·
    refine ⟨199267079028989760958991933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132844719352659840639327955 199267079028989760958991933)
    ·
      refine ⟨74725154635871160359621975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199267079028989760958991933 74725154635871160359621975)
      ·
        refine ⟨112087731953806740539432963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74725154635871160359621975 112087731953806740539432963)
        ·
          refine ⟨168131597930710110809149445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112087731953806740539432963 168131597930710110809149445)
          ·
            refine ⟨31524674612008145776715521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168131597930710110809149445 31524674612008145776715521)
            ·
              refine ⟨23643505959006109332536641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31524674612008145776715521 23643505959006109332536641)
              ·
                refine ⟨17732629469254581999402481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23643505959006109332536641 17732629469254581999402481)
                ·
                  refine ⟨13299472101940936499551861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17732629469254581999402481 13299472101940936499551861)
                  ·
                    refine ⟨1246825509556962796832987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13299472101940936499551861 1246825509556962796832987)
                    ·
                      rfl

theorem cell23_7284552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_7284552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284552 prefixEnd_7284552 := by exact prefixLift 7284552
  have htrace : WordTrace (prefixWord ++ tailWord_7284552) baseStart_7284552 baseEnd_7284552 := by
    simpa [prefixWord, tailWord_7284552, baseEnd_7284552] using wordTrace_append hprefix tailTrace_7284552
  have hstable : (prefixWord ++ tailWord_7284552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284552).length < 2 ^ (prefixWord ++ tailWord_7284552).sum := by decide
  have hdescent : baseEnd_7284552 < baseStart_7284552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284562 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_7284562 : Nat := 118140960795 + 7284562 * 2 ^ 59
def prefixEnd_7284562 : Nat := 4983230072969 + 3 ^ 40 * 7284562 * 2
def baseEnd_7284562 : Nat := 3740481663477433351373915

theorem tailTrace_7284562 : CollatzResearch.WordTrace tailWord_7284562 prefixEnd_7284562 3740481663477433351373915 := by
  unfold tailWord_7284562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66422450858820863246629985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177126535623522301991013293 66422450858820863246629985)
  ·
    refine ⟨49816838144115647434972489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66422450858820863246629985 49816838144115647434972489)
    ·
      refine ⟨37362628608086735576229367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49816838144115647434972489 37362628608086735576229367)
      ·
        refine ⟨56043942912130103364344051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37362628608086735576229367 56043942912130103364344051)
        ·
          refine ⟨84065914368195155046516077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56043942912130103364344051 84065914368195155046516077)
          ·
            refine ⟨31524717888073183142443529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84065914368195155046516077 31524717888073183142443529)
            ·
              refine ⟨23643538416054887356832647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31524717888073183142443529 23643538416054887356832647)
              ·
                refine ⟨35465307624082331035248971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23643538416054887356832647 35465307624082331035248971)
                ·
                  refine ⟨53197961436123496552873457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35465307624082331035248971 53197961436123496552873457)
                  ·
                    refine ⟨39898471077092622414655093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53197961436123496552873457 39898471077092622414655093)
                    ·
                      refine ⟨3740481663477433351373915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39898471077092622414655093 3740481663477433351373915)
                      ·
                        rfl

theorem cell23_7284562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_7284562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284562 prefixEnd_7284562 := by exact prefixLift 7284562
  have htrace : WordTrace (prefixWord ++ tailWord_7284562) baseStart_7284562 baseEnd_7284562 := by
    simpa [prefixWord, tailWord_7284562, baseEnd_7284562] using wordTrace_append hprefix tailTrace_7284562
  have hstable : (prefixWord ++ tailWord_7284562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284562).length < 2 ^ (prefixWord ++ tailWord_7284562).sum := by decide
  have hdescent : baseEnd_7284562 < baseStart_7284562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284585 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_7284585 : Nat := 118140960795 + 7284585 * 2 ^ 59
def prefixEnd_7284585 : Nat := 4983230072969 + 3 ^ 40 * 7284585 * 2
def baseEnd_7284585 : Nat := 3740493473532486761386309

theorem tailTrace_7284585 : CollatzResearch.WordTrace tailWord_7284585 prefixEnd_7284585 3740493473532486761386309 := by
  unfold tailWord_7284585
  simp only [CollatzResearch.WordTrace]
  refine ⟨265690642314200127914607209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177127094876133418609738139 265690642314200127914607209)
  ·
    refine ⟨199267981735650095935955407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265690642314200127914607209 199267981735650095935955407)
    ·
      refine ⟨298901972603475143903933111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199267981735650095935955407 298901972603475143903933111)
      ·
        refine ⟨448352958905212715855899667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298901972603475143903933111 448352958905212715855899667)
        ·
          refine ⟨672529438357819073783849501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448352958905212715855899667 672529438357819073783849501)
          ·
            refine ⟨252198539384182152668943563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672529438357819073783849501 252198539384182152668943563)
            ·
              refine ⟨378297809076273229003415345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252198539384182152668943563 378297809076273229003415345)
              ·
                refine ⟨283723356807204921752561509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378297809076273229003415345 283723356807204921752561509)
                ·
                  refine ⟨53198129401350922828605283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283723356807204921752561509 53198129401350922828605283)
                  ·
                    refine ⟨79797194102026384242907925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53198129401350922828605283 79797194102026384242907925)
                    ·
                      refine ⟨3740493473532486761386309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79797194102026384242907925 3740493473532486761386309)
                      ·
                        rfl

theorem cell23_7284585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_7284585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284585 prefixEnd_7284585 := by exact prefixLift 7284585
  have htrace : WordTrace (prefixWord ++ tailWord_7284585) baseStart_7284585 baseEnd_7284585 := by
    simpa [prefixWord, tailWord_7284585, baseEnd_7284585] using wordTrace_append hprefix tailTrace_7284585
  have hstable : (prefixWord ++ tailWord_7284585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284585).length < 2 ^ (prefixWord ++ tailWord_7284585).sum := by decide
  have hdescent : baseEnd_7284585 < baseStart_7284585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284589 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7284589 : Nat := 118140960795 + 7284589 * 2 ^ 59
def prefixEnd_7284589 : Nat := 4983230072969 + 3 ^ 40 * 7284589 * 2
def baseEnd_7284589 : Nat := 3740495527455104745736291

theorem tailTrace_7284589 : CollatzResearch.WordTrace tailWord_7284589 prefixEnd_7284589 3740495527455104745736291 := by
  unfold tailWord_7284589
  simp only [CollatzResearch.WordTrace]
  refine ⟨265690788206185636597752821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177127192137457091065168547 265690788206185636597752821)
  ·
    refine ⟨24908511394329903431039327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265690788206185636597752821 24908511394329903431039327)
    ·
      refine ⟨37362767091494855146558991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24908511394329903431039327 37362767091494855146558991)
      ·
        refine ⟨56044150637242282719838487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37362767091494855146558991 56044150637242282719838487)
        ·
          refine ⟨84066225955863424079757731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56044150637242282719838487 84066225955863424079757731)
          ·
            refine ⟨126099338933795136119636597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84066225955863424079757731 126099338933795136119636597)
            ·
              refine ⟨11821813025043294011215931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126099338933795136119636597 11821813025043294011215931)
              ·
                refine ⟨17732719537564941016823897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11821813025043294011215931 17732719537564941016823897)
                ·
                  refine ⟨13299539653173705762617923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17732719537564941016823897 13299539653173705762617923)
                  ·
                    refine ⟨19949309479760558643926885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13299539653173705762617923 19949309479760558643926885)
                    ·
                      refine ⟨3740495527455104745736291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19949309479760558643926885 3740495527455104745736291)
                      ·
                        rfl

theorem cell23_7284589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7284589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284589 prefixEnd_7284589 := by exact prefixLift 7284589
  have htrace : WordTrace (prefixWord ++ tailWord_7284589) baseStart_7284589 baseEnd_7284589 := by
    simpa [prefixWord, tailWord_7284589, baseEnd_7284589] using wordTrace_append hprefix tailTrace_7284589
  have hstable : (prefixWord ++ tailWord_7284589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284589).length < 2 ^ (prefixWord ++ tailWord_7284589).sum := by decide
  have hdescent : baseEnd_7284589 < baseStart_7284589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284595 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 8]
def baseStart_7284595 : Nat := 118140960795 + 7284595 * 2 ^ 59
def prefixEnd_7284595 : Nat := 4983230072969 + 3 ^ 40 * 7284595 * 2
def baseEnd_7284595 : Nat := 415610956482114635806807

theorem tailTrace_7284595 : CollatzResearch.WordTrace tailWord_7284595 prefixEnd_7284595 415610956482114635806807 := by
  unfold tailWord_7284595
  simp only [CollatzResearch.WordTrace]
  refine ⟨265691007044163899622471239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177127338029442599748314159 265691007044163899622471239)
  ·
    refine ⟨398536510566245849433706859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265691007044163899622471239 398536510566245849433706859)
    ·
      refine ⟨597804765849368774150560289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398536510566245849433706859 597804765849368774150560289)
      ·
        refine ⟨448353574387026580612920217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597804765849368774150560289 448353574387026580612920217)
        ·
          refine ⟨336265180790269935459690163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448353574387026580612920217 336265180790269935459690163)
          ·
            refine ⟨504397771185404903189535245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336265180790269935459690163 504397771185404903189535245)
            ·
              refine ⟨189149164194526838696075717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504397771185404903189535245 189149164194526838696075717)
              ·
                refine ⟨35465468286473782255514197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189149164194526838696075717 35465468286473782255514197)
                ·
                  refine ⟨415610956482114635806807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35465468286473782255514197 415610956482114635806807)
                  ·
                    rfl

theorem cell23_7284595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 8].length) (baseStart_7284595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284595 prefixEnd_7284595 := by exact prefixLift 7284595
  have htrace : WordTrace (prefixWord ++ tailWord_7284595) baseStart_7284595 baseEnd_7284595 := by
    simpa [prefixWord, tailWord_7284595, baseEnd_7284595] using wordTrace_append hprefix tailTrace_7284595
  have hstable : (prefixWord ++ tailWord_7284595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284595).length < 2 ^ (prefixWord ++ tailWord_7284595).sum := by decide
  have hdescent : baseEnd_7284595 < baseStart_7284595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284616 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 3, 4]
def baseStart_7284616 : Nat := 118140960795 + 7284616 * 2 ^ 59
def prefixEnd_7284616 : Nat := 4983230072969 + 3 ^ 40 * 7284616 * 2
def baseEnd_7284616 : Nat := 1246836463810925380032889

theorem tailTrace_7284616 : CollatzResearch.WordTrace tailWord_7284616 prefixEnd_7284616 1246836463810925380032889 := by
  unfold tailWord_7284616
  simp only [CollatzResearch.WordTrace]
  refine ⟨132845886488543910104492851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177127848651391880139323801 132845886488543910104492851)
  ·
    refine ⟨199268829732815865156739277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132845886488543910104492851 199268829732815865156739277)
    ·
      refine ⟨74725811149805949433777229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199268829732815865156739277 74725811149805949433777229)
      ·
        refine ⟨28022179181177231037666461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74725811149805949433777229 28022179181177231037666461)
        ·
          refine ⟨10508317192941461639124923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28022179181177231037666461 10508317192941461639124923)
          ·
            refine ⟨15762475789412192458687385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10508317192941461639124923 15762475789412192458687385)
            ·
              refine ⟨11821856842059144344015539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15762475789412192458687385 11821856842059144344015539)
              ·
                refine ⟨17732785263088716516023309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11821856842059144344015539 17732785263088716516023309)
                ·
                  refine ⟨6649794473658268693508741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17732785263088716516023309 6649794473658268693508741)
                  ·
                    refine ⟨1246836463810925380032889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6649794473658268693508741 1246836463810925380032889)
                    ·
                      rfl

theorem cell23_7284616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_7284616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284616 prefixEnd_7284616 := by exact prefixLift 7284616
  have htrace : WordTrace (prefixWord ++ tailWord_7284616) baseStart_7284616 baseEnd_7284616 := by
    simpa [prefixWord, tailWord_7284616, baseEnd_7284616] using wordTrace_append hprefix tailTrace_7284616
  have hstable : (prefixWord ++ tailWord_7284616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284616).length < 2 ^ (prefixWord ++ tailWord_7284616).sum := by decide
  have hdescent : baseEnd_7284616 < baseStart_7284616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284629 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 6]
def baseStart_7284629 : Nat := 118140960795 + 7284629 * 2 ^ 59
def prefixEnd_7284629 : Nat := 4983230072969 + 3 ^ 40 * 7284629 * 2
def baseEnd_7284629 : Nat := 415612896297920509915123

theorem tailTrace_7284629 : CollatzResearch.WordTrace tailWord_7284629 prefixEnd_7284629 415612896297920509915123 := by
  unfold tailWord_7284629
  simp only [CollatzResearch.WordTrace]
  refine ⟨265692247126040723429208941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177128164750693815619472627 265692247126040723429208941)
  ·
    refine ⟨99634592672265271285953353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265692247126040723429208941 99634592672265271285953353)
    ·
      refine ⟨74725944504198953464465015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99634592672265271285953353 74725944504198953464465015)
      ·
        refine ⟨112088916756298430196697523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74725944504198953464465015 112088916756298430196697523)
        ·
          refine ⟨168133375134447645295046285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112088916756298430196697523 168133375134447645295046285)
          ·
            refine ⟨63050015675417866985642357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168133375134447645295046285 63050015675417866985642357)
            ·
              refine ⟨5910938969570425029903971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63050015675417866985642357 5910938969570425029903971)
              ·
                refine ⟨8866408454355637544855957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910938969570425029903971 8866408454355637544855957)
                ·
                  refine ⟨415612896297920509915123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8866408454355637544855957 415612896297920509915123)
                  ·
                    rfl

theorem cell23_7284629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_7284629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284629 prefixEnd_7284629 := by exact prefixLift 7284629
  have htrace : WordTrace (prefixWord ++ tailWord_7284629) baseStart_7284629 baseEnd_7284629 := by
    simpa [prefixWord, tailWord_7284629, baseEnd_7284629] using wordTrace_append hprefix tailTrace_7284629
  have hstable : (prefixWord ++ tailWord_7284629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284629).length < 2 ^ (prefixWord ++ tailWord_7284629).sum := by decide
  have hdescent : baseEnd_7284629 < baseStart_7284629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284696 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 5, 2, 2]
def baseStart_7284696 : Nat := 118140960795 + 7284696 * 2 ^ 59
def prefixEnd_7284696 : Nat := 4983230072969 + 3 ^ 40 * 7284696 * 2
def baseEnd_7284696 : Nat := 3740550469885135827098299

theorem tailTrace_7284696 : CollatzResearch.WordTrace tailWord_7284696 prefixEnd_7284696 3740550469885135827098299 := by
  unfold tailWord_7284696
  simp only [CollatzResearch.WordTrace]
  refine ⟨132847345408398996935948971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177129793877865329247931961 132847345408398996935948971)
  ·
    refine ⟨199271018112598495403923457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132847345408398996935948971 199271018112598495403923457)
    ·
      refine ⟨149453263584448871552942593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199271018112598495403923457 149453263584448871552942593)
      ·
        refine ⟨112089947688336653664706945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149453263584448871552942593 112089947688336653664706945)
        ·
          refine ⟨84067460766252490248530209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112089947688336653664706945 84067460766252490248530209)
          ·
            refine ⟨63050595574689367686397657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84067460766252490248530209 63050595574689367686397657)
            ·
              refine ⟨47287946681017025764798243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63050595574689367686397657 47287946681017025764798243)
              ·
                refine ⟨70931920021525538647197365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47287946681017025764798243 70931920021525538647197365)
                ·
                  refine ⟨6649867502018019248174753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70931920021525538647197365 6649867502018019248174753)
                  ·
                    refine ⟨4987400626513514436131065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649867502018019248174753 4987400626513514436131065)
                    ·
                      refine ⟨3740550469885135827098299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987400626513514436131065 3740550469885135827098299)
                      ·
                        rfl

theorem cell23_7284696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_7284696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284696 prefixEnd_7284696 := by exact prefixLift 7284696
  have htrace : WordTrace (prefixWord ++ tailWord_7284696) baseStart_7284696 baseEnd_7284696 := by
    simpa [prefixWord, tailWord_7284696, baseEnd_7284696] using wordTrace_append hprefix tailTrace_7284696
  have hstable : (prefixWord ++ tailWord_7284696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284696).length < 2 ^ (prefixWord ++ tailWord_7284696).sum := by decide
  have hdescent : baseEnd_7284696 < baseStart_7284696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284732 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_7284732 : Nat := 118140960795 + 7284732 * 2 ^ 59
def prefixEnd_7284732 : Nat := 4983230072969 + 3 ^ 40 * 7284732 * 2
def baseEnd_7284732 : Nat := 1246856318396232562082711

theorem tailTrace_7284732 : CollatzResearch.WordTrace tailWord_7284732 prefixEnd_7284732 1246856318396232562082711 := by
  unfold tailWord_7284732
  simp only [CollatzResearch.WordTrace]
  refine ⟨132848001922333786010104225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177130669229778381346805633 132848001922333786010104225)
  ·
    refine ⟨99636001441750339507578169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132848001922333786010104225 99636001441750339507578169)
    ·
      refine ⟨74727001081312754630683627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99636001441750339507578169 74727001081312754630683627)
      ·
        refine ⟨112090501621969131946025441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74727001081312754630683627 112090501621969131946025441)
        ·
          refine ⟨84067876216476848959519081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112090501621969131946025441 84067876216476848959519081)
          ·
            refine ⟨63050907162357636719639311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84067876216476848959519081 63050907162357636719639311)
            ·
              refine ⟨94576360743536455079458967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63050907162357636719639311 94576360743536455079458967)
              ·
                refine ⟨141864541115304682619188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94576360743536455079458967 141864541115304682619188451)
                ·
                  refine ⟨212796811672957023928782677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141864541115304682619188451 212796811672957023928782677)
                  ·
                    refine ⟨1246856318396232562082711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 212796811672957023928782677 1246856318396232562082711)
                    ·
                      rfl

theorem cell23_7284732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_7284732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284732 prefixEnd_7284732 := by exact prefixLift 7284732
  have htrace : WordTrace (prefixWord ++ tailWord_7284732) baseStart_7284732 baseEnd_7284732 := by
    simpa [prefixWord, tailWord_7284732, baseEnd_7284732] using wordTrace_append hprefix tailTrace_7284732
  have hstable : (prefixWord ++ tailWord_7284732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284732).length < 2 ^ (prefixWord ++ tailWord_7284732).sum := by decide
  have hdescent : baseEnd_7284732 < baseStart_7284732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284773 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 1, 3, 2]
def baseStart_7284773 : Nat := 118140960795 + 7284773 * 2 ^ 59
def prefixEnd_7284773 : Nat := 4983230072969 + 3 ^ 40 * 7284773 * 2
def baseEnd_7284773 : Nat := 3740590007895532025835445

theorem tailTrace_7284773 : CollatzResearch.WordTrace tailWord_7284773 prefixEnd_7284773 3740590007895532025835445 := by
  unfold tailWord_7284773
  simp only [CollatzResearch.WordTrace]
  refine ⟨265697499237519036022450973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177131666158346024014967315 265697499237519036022450973)
  ·
    refine ⟨99636562214069638508419115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265697499237519036022450973 99636562214069638508419115)
    ·
      refine ⟨149454843321104457762628673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99636562214069638508419115 149454843321104457762628673)
      ·
        refine ⟨112091132490828343321971505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149454843321104457762628673 112091132490828343321971505)
        ·
          refine ⟨84068349368121257491478629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112091132490828343321971505 84068349368121257491478629)
          ·
            refine ⟨15762815506522735779652243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84068349368121257491478629 15762815506522735779652243)
            ·
              refine ⟨23644223259784103669478365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15762815506522735779652243 23644223259784103669478365)
              ·
                refine ⟨8866583722419038876054387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23644223259784103669478365 8866583722419038876054387)
                ·
                  refine ⟨13299875583628558314081581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8866583722419038876054387 13299875583628558314081581)
                  ·
                    refine ⟨4987453343860709367780593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13299875583628558314081581 4987453343860709367780593)
                    ·
                      refine ⟨3740590007895532025835445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987453343860709367780593 3740590007895532025835445)
                      ·
                        rfl

theorem cell23_7284773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_7284773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284773 prefixEnd_7284773 := by exact prefixLift 7284773
  have htrace : WordTrace (prefixWord ++ tailWord_7284773) baseStart_7284773 baseEnd_7284773 := by
    simpa [prefixWord, tailWord_7284773, baseEnd_7284773] using wordTrace_append hprefix tailTrace_7284773
  have hstable : (prefixWord ++ tailWord_7284773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284773).length < 2 ^ (prefixWord ++ tailWord_7284773).sum := by decide
  have hdescent : baseEnd_7284773 < baseStart_7284773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284789 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_7284789 : Nat := 118140960795 + 7284789 * 2 ^ 59
def prefixEnd_7284789 : Nat := 4983230072969 + 3 ^ 40 * 7284789 * 2
def baseEnd_7284789 : Nat := 3740598223586003963235371

theorem tailTrace_7284789 : CollatzResearch.WordTrace tailWord_7284789 prefixEnd_7284789 3740598223586003963235371 := by
  unfold tailWord_7284789
  simp only [CollatzResearch.WordTrace]
  refine ⟨265698082805461070755033421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177132055203640713836688947 265698082805461070755033421)
  ·
    refine ⟨99636781052047901533137533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265698082805461070755033421 99636781052047901533137533)
    ·
      refine ⟨37363792894517963074926575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99636781052047901533137533 37363792894517963074926575)
      ·
        refine ⟨56045689341776944612389863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37363792894517963074926575 56045689341776944612389863)
        ·
          refine ⟨84068534012665416918584795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56045689341776944612389863 84068534012665416918584795)
          ·
            refine ⟨126102801018998125377877193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84068534012665416918584795 126102801018998125377877193)
            ·
              refine ⟨94577100764248594033407895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126102801018998125377877193 94577100764248594033407895)
              ·
                refine ⟨141865651146372891050111843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94577100764248594033407895 141865651146372891050111843)
                ·
                  refine ⟨212798476719559336575167765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141865651146372891050111843 212798476719559336575167765)
                  ·
                    refine ⟨9974928596229343901960989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212798476719559336575167765 9974928596229343901960989)
                    ·
                      refine ⟨3740598223586003963235371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9974928596229343901960989 3740598223586003963235371)
                      ·
                        rfl

theorem cell23_7284789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_7284789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284789 prefixEnd_7284789 := by exact prefixLift 7284789
  have htrace : WordTrace (prefixWord ++ tailWord_7284789) baseStart_7284789 baseEnd_7284789 := by
    simpa [prefixWord, tailWord_7284789, baseEnd_7284789] using wordTrace_append hprefix tailTrace_7284789
  have hstable : (prefixWord ++ tailWord_7284789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284789).length < 2 ^ (prefixWord ++ tailWord_7284789).sum := by decide
  have hdescent : baseEnd_7284789 < baseStart_7284789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284799 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_7284799 : Nat := 118140960795 + 7284799 * 2 ^ 59
def prefixEnd_7284799 : Nat := 4983230072969 + 3 ^ 40 * 7284799 * 2
def baseEnd_7284799 : Nat := 3740603358392548924110325

theorem tailTrace_7284799 : CollatzResearch.WordTrace tailWord_7284799 prefixEnd_7284799 3740603358392548924110325 := by
  unfold tailWord_7284799
  simp only [CollatzResearch.WordTrace]
  refine ⟨265698447535424842462897451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177132298356949894975264967 265698447535424842462897451)
  ·
    refine ⟨398547671303137263694346177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265698447535424842462897451 398547671303137263694346177)
    ·
      refine ⟨298910753477352947770759633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398547671303137263694346177 298910753477352947770759633)
      ·
        refine ⟨224183065108014710828069725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298910753477352947770759633 224183065108014710828069725)
        ·
          refine ⟨84068649415505516560526147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224183065108014710828069725 84068649415505516560526147)
          ·
            refine ⟨126102974123258274840789221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84068649415505516560526147 126102974123258274840789221)
            ·
              refine ⟨23644307648110926532647979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126102974123258274840789221 23644307648110926532647979)
              ·
                refine ⟨35466461472166389798971969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23644307648110926532647979 35466461472166389798971969)
                ·
                  refine ⟨26599846104124792349228977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35466461472166389798971969 26599846104124792349228977)
                  ·
                    refine ⟨19949884578093594261921733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26599846104124792349228977 19949884578093594261921733)
                    ·
                      refine ⟨3740603358392548924110325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19949884578093594261921733 3740603358392548924110325)
                      ·
                        rfl

theorem cell23_7284799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_7284799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284799 prefixEnd_7284799 := by exact prefixLift 7284799
  have htrace : WordTrace (prefixWord ++ tailWord_7284799) baseStart_7284799 baseEnd_7284799 := by
    simpa [prefixWord, tailWord_7284799, baseEnd_7284799] using wordTrace_append hprefix tailTrace_7284799
  have hstable : (prefixWord ++ tailWord_7284799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284799).length < 2 ^ (prefixWord ++ tailWord_7284799).sum := by decide
  have hdescent : baseEnd_7284799 < baseStart_7284799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284849 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_7284849 : Nat := 118140960795 + 7284849 * 2 ^ 59
def prefixEnd_7284849 : Nat := 4983230072969 + 3 ^ 40 * 7284849 * 2
def baseEnd_7284849 : Nat := 3740629032425273728485095

theorem tailTrace_7284849 : CollatzResearch.WordTrace tailWord_7284849 prefixEnd_7284849 3740629032425273728485095 := by
  unfold tailWord_7284849
  simp only [CollatzResearch.WordTrace]
  refine ⟨265700271185243701002217601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177133514123495800668145067 265700271185243701002217601)
  ·
    refine ⟨199275203388932775751663201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265700271185243701002217601 199275203388932775751663201)
    ·
      refine ⟨149456402541699581813747401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199275203388932775751663201 149456402541699581813747401)
      ·
        refine ⟨112092301906274686360310551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149456402541699581813747401 112092301906274686360310551)
        ·
          refine ⟨168138452859412029540465827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112092301906274686360310551 168138452859412029540465827)
          ·
            refine ⟨252207679289118044310698741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168138452859412029540465827 252207679289118044310698741)
            ·
              refine ⟨23644469933354816654128007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252207679289118044310698741 23644469933354816654128007)
              ·
                refine ⟨35466704900032224981192011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23644469933354816654128007 35466704900032224981192011)
                ·
                  refine ⟨53200057350048337471788017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35466704900032224981192011 53200057350048337471788017)
                  ·
                    refine ⟨39900043012536253103841013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53200057350048337471788017 39900043012536253103841013)
                    ·
                      refine ⟨3740629032425273728485095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39900043012536253103841013 3740629032425273728485095)
                      ·
                        rfl

theorem cell23_7284849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_7284849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284849 prefixEnd_7284849 := by exact prefixLift 7284849
  have htrace : WordTrace (prefixWord ++ tailWord_7284849) baseStart_7284849 baseEnd_7284849 := by
    simpa [prefixWord, tailWord_7284849, baseEnd_7284849] using wordTrace_append hprefix tailTrace_7284849
  have hstable : (prefixWord ++ tailWord_7284849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284849).length < 2 ^ (prefixWord ++ tailWord_7284849).sum := by decide
  have hdescent : baseEnd_7284849 < baseStart_7284849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284854 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7284854 : Nat := 118140960795 + 7284854 * 2 ^ 59
def prefixEnd_7284854 : Nat := 4983230072969 + 3 ^ 40 * 7284854 * 2
def baseEnd_7284854 : Nat := 3740631599828546208922573

theorem tailTrace_7284854 : CollatzResearch.WordTrace tailWord_7284854 prefixEnd_7284854 3740631599828546208922573 := by
  unfold tailWord_7284854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606278346889099178509351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177133635700150391237433077 16606278346889099178509351)
  ·
    refine ⟨24909417520333648767764027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16606278346889099178509351 24909417520333648767764027)
    ·
      refine ⟨37364126280500473151646041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24909417520333648767764027 37364126280500473151646041)
      ·
        refine ⟨28023094710375354863734531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37364126280500473151646041 28023094710375354863734531)
        ·
          refine ⟨42034642065563032295601797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28023094710375354863734531 42034642065563032295601797)
          ·
            refine ⟨7881495387293068555425337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42034642065563032295601797 7881495387293068555425337)
            ·
              refine ⟨5911121540469801416569003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881495387293068555425337 5911121540469801416569003)
              ·
                refine ⟨8866682310704702124853505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911121540469801416569003 8866682310704702124853505)
                ·
                  refine ⟨6650011733028526593640129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866682310704702124853505 6650011733028526593640129)
                  ·
                    refine ⟨4987508799771394945230097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6650011733028526593640129 4987508799771394945230097)
                    ·
                      refine ⟨3740631599828546208922573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987508799771394945230097 3740631599828546208922573)
                      ·
                        rfl

theorem cell23_7284854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7284854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284854 prefixEnd_7284854 := by exact prefixLift 7284854
  have htrace : WordTrace (prefixWord ++ tailWord_7284854) baseStart_7284854 baseEnd_7284854 := by
    simpa [prefixWord, tailWord_7284854, baseEnd_7284854] using wordTrace_append hprefix tailTrace_7284854
  have hstable : (prefixWord ++ tailWord_7284854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284854).length < 2 ^ (prefixWord ++ tailWord_7284854).sum := by decide
  have hdescent : baseEnd_7284854 < baseStart_7284854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284876 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 6, 4, 2]
def baseStart_7284876 : Nat := 118140960795 + 7284876 * 2 ^ 59
def prefixEnd_7284876 : Nat := 4983230072969 + 3 ^ 40 * 7284876 * 2
def baseEnd_7284876 : Nat := 3740642896402945122847471

theorem tailTrace_7284876 : CollatzResearch.WordTrace tailWord_7284876 prefixEnd_7284876 3740642896402945122847471 := by
  unfold tailWord_7284876
  simp only [CollatzResearch.WordTrace]
  refine ⟨132850627978072942306725241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177134170637430589742300321 132850627978072942306725241)
  ·
    refine ⟨99637970983554706730043931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132850627978072942306725241 99637970983554706730043931)
    ·
      refine ⟨149456956475332060095065897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99637970983554706730043931 149456956475332060095065897)
      ·
        refine ⟨112092717356499045071299423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149456956475332060095065897 112092717356499045071299423)
        ·
          refine ⟨168139076034748567606949135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112092717356499045071299423 168139076034748567606949135)
          ·
            refine ⟨252208614052122851410423703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168139076034748567606949135 252208614052122851410423703)
            ·
              refine ⟨378312921078184277115635555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252208614052122851410423703 378312921078184277115635555)
              ·
                refine ⟨567469381617276415673453333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378312921078184277115635555 567469381617276415673453333)
                ·
                  refine ⟨26600127263309831984693125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 567469381617276415673453333 26600127263309831984693125)
                  ·
                    refine ⟨4987523861870593497129961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26600127263309831984693125 4987523861870593497129961)
                    ·
                      refine ⟨3740642896402945122847471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987523861870593497129961 3740642896402945122847471)
                      ·
                        rfl

theorem cell23_7284876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_7284876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284876 prefixEnd_7284876 := by exact prefixLift 7284876
  have htrace : WordTrace (prefixWord ++ tailWord_7284876) baseStart_7284876 baseEnd_7284876 := by
    simpa [prefixWord, tailWord_7284876, baseEnd_7284876] using wordTrace_append hprefix tailTrace_7284876
  have hstable : (prefixWord ++ tailWord_7284876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284876).length < 2 ^ (prefixWord ++ tailWord_7284876).sum := by decide
  have hdescent : baseEnd_7284876 < baseStart_7284876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284894 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_7284894 : Nat := 118140960795 + 7284894 * 2 ^ 59
def prefixEnd_7284894 : Nat := 4983230072969 + 3 ^ 40 * 7284894 * 2
def baseEnd_7284894 : Nat := 415628015450525116935821

theorem tailTrace_7284894 : CollatzResearch.WordTrace tailWord_7284894 prefixEnd_7284894 415628015450525116935821 := by
  unfold tailWord_7284894
  simp only [CollatzResearch.WordTrace]
  refine ⟨33212739058760084210950717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177134608313387115791737157 33212739058760084210950717)
  ·
    refine ⟨12454777147035031579106519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33212739058760084210950717 12454777147035031579106519)
    ·
      refine ⟨18682165720552547368659779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12454777147035031579106519 18682165720552547368659779)
      ·
        refine ⟨28023248580828821052989669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18682165720552547368659779 28023248580828821052989669)
        ·
          refine ⟨5254359108905403947435563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28023248580828821052989669 5254359108905403947435563)
          ·
            refine ⟨7881538663358105921153345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254359108905403947435563 7881538663358105921153345)
            ·
              refine ⟨5911153997518579440865009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881538663358105921153345 5911153997518579440865009)
              ·
                refine ⟨4433365498138934580648757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911153997518579440865009 4433365498138934580648757)
                ·
                  refine ⟨415628015450525116935821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4433365498138934580648757 415628015450525116935821)
                  ·
                    rfl

theorem cell23_7284894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_7284894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284894 prefixEnd_7284894 := by exact prefixLift 7284894
  have htrace : WordTrace (prefixWord ++ tailWord_7284894) baseStart_7284894 baseEnd_7284894 := by
    simpa [prefixWord, tailWord_7284894, baseEnd_7284894] using wordTrace_append hprefix tailTrace_7284894
  have hstable : (prefixWord ++ tailWord_7284894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284894).length < 2 ^ (prefixWord ++ tailWord_7284894).sum := by decide
  have hdescent : baseEnd_7284894 < baseStart_7284894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284950 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7284950 : Nat := 118140960795 + 7284950 * 2 ^ 59
def prefixEnd_7284950 : Nat := 4983230072969 + 3 ^ 40 * 7284950 * 2
def baseEnd_7284950 : Nat := 415631210441264203702459

theorem tailTrace_7284950 : CollatzResearch.WordTrace tailWord_7284950 prefixEnd_7284950 415631210441264203702459 := by
  unfold tailWord_7284950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606497184867362203227769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177135969971918530167762869 16606497184867362203227769)
  ·
    refine ⟨12454872888650521652420827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16606497184867362203227769 12454872888650521652420827)
    ·
      refine ⟨18682309332975782478631241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12454872888650521652420827 18682309332975782478631241)
      ·
        refine ⟨14011731999731836858973431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18682309332975782478631241 14011731999731836858973431)
        ·
          refine ⟨21017597999597755288460147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14011731999731836858973431 21017597999597755288460147)
          ·
            refine ⟨31526396999396632932690221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21017597999597755288460147 31526396999396632932690221)
            ·
              refine ⟨11822398874773737349758833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31526396999396632932690221 11822398874773737349758833)
              ·
                refine ⟨8866799156080303012319125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11822398874773737349758833 8866799156080303012319125)
                ·
                  refine ⟨415631210441264203702459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8866799156080303012319125 415631210441264203702459)
                  ·
                    rfl

theorem cell23_7284950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7284950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284950 prefixEnd_7284950 := by exact prefixLift 7284950
  have htrace : WordTrace (prefixWord ++ tailWord_7284950) baseStart_7284950 baseEnd_7284950 := by
    simpa [prefixWord, tailWord_7284950, baseEnd_7284950] using wordTrace_append hprefix tailTrace_7284950
  have hstable : (prefixWord ++ tailWord_7284950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284950).length < 2 ^ (prefixWord ++ tailWord_7284950).sum := by decide
  have hdescent : baseEnd_7284950 < baseStart_7284950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284953 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 2, 3, 2]
def baseStart_7284953 : Nat := 118140960795 + 7284953 * 2 ^ 59
def prefixEnd_7284953 : Nat := 4983230072969 + 3 ^ 40 * 7284953 * 2
def baseEnd_7284953 : Nat := 3740682434413341321584617

theorem tailTrace_7284953 : CollatzResearch.WordTrace tailWord_7284953 prefixEnd_7284953 3740682434413341321584617 := by
  unfold tailWord_7284953
  simp only [CollatzResearch.WordTrace]
  refine ⟨265704064376866926764003513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177136042917911284509335675 265704064376866926764003513)
  ·
    refine ⟨199278048282650195073002635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265704064376866926764003513 199278048282650195073002635)
    ·
      refine ⟨298917072423975292609503953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199278048282650195073002635 298917072423975292609503953)
      ·
        refine ⟨224187804317981469457127965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298917072423975292609503953 224187804317981469457127965)
        ·
          refine ⟨84070426619243051046422987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224187804317981469457127965 84070426619243051046422987)
          ·
            refine ⟨126105639928864576569634481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84070426619243051046422987 126105639928864576569634481)
            ·
              refine ⟨94579229946648432427225861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126105639928864576569634481 94579229946648432427225861)
              ·
                refine ⟨17733605614996581080104849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94579229946648432427225861 17733605614996581080104849)
                ·
                  refine ⟨13300204211247435810078637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17733605614996581080104849 13300204211247435810078637)
                  ·
                    refine ⟨4987576579217788428779489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13300204211247435810078637 4987576579217788428779489)
                    ·
                      refine ⟨3740682434413341321584617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987576579217788428779489 3740682434413341321584617)
                      ·
                        rfl

theorem cell23_7284953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_7284953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284953 prefixEnd_7284953 := by exact prefixLift 7284953
  have htrace : WordTrace (prefixWord ++ tailWord_7284953) baseStart_7284953 baseEnd_7284953 := by
    simpa [prefixWord, tailWord_7284953, baseEnd_7284953] using wordTrace_append hprefix tailTrace_7284953
  have hstable : (prefixWord ++ tailWord_7284953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284953).length < 2 ^ (prefixWord ++ tailWord_7284953).sum := by decide
  have hdescent : baseEnd_7284953 < baseStart_7284953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284960 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 1, 1, 3]
def baseStart_7284960 : Nat := 118140960795 + 7284960 * 2 ^ 59
def prefixEnd_7284960 : Nat := 4983230072969 + 3 ^ 40 * 7284960 * 2
def baseEnd_7284960 : Nat := 3740686028777922794197085

theorem tailTrace_7284960 : CollatzResearch.WordTrace tailWord_7284960 prefixEnd_7284960 3740686028777922794197085 := by
  unfold tailWord_7284960
  simp only [CollatzResearch.WordTrace]
  refine ⟨132852159843920783479754167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177136213125227711306338889 132852159843920783479754167)
  ·
    refine ⟨199278239765881175219631251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132852159843920783479754167 199278239765881175219631251)
    ·
      refine ⟨298917359648821762829446877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199278239765881175219631251 298917359648821762829446877)
      ·
        refine ⟨112094009868308161061042579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298917359648821762829446877 112094009868308161061042579)
        ·
          refine ⟨168141014802462241591563869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112094009868308161061042579 168141014802462241591563869)
          ·
            refine ⟨63052880550923340596836451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168141014802462241591563869 63052880550923340596836451)
            ·
              refine ⟨94579320826385010895254677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63052880550923340596836451 94579320826385010895254677)
              ·
                refine ⟨4433405663736797385715063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94579320826385010895254677 4433405663736797385715063)
                ·
                  refine ⟨6650108495605196078572595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4433405663736797385715063 6650108495605196078572595)
                  ·
                    refine ⟨9975162743407794117858893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6650108495605196078572595 9975162743407794117858893)
                    ·
                      refine ⟨3740686028777922794197085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9975162743407794117858893 3740686028777922794197085)
                      ·
                        rfl

theorem cell23_7284960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_7284960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284960 prefixEnd_7284960 := by exact prefixLift 7284960
  have htrace : WordTrace (prefixWord ++ tailWord_7284960) baseStart_7284960 baseEnd_7284960 := by
    simpa [prefixWord, tailWord_7284960, baseEnd_7284960] using wordTrace_append hprefix tailTrace_7284960
  have hstable : (prefixWord ++ tailWord_7284960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284960).length < 2 ^ (prefixWord ++ tailWord_7284960).sum := by decide
  have hdescent : baseEnd_7284960 < baseStart_7284960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7284994 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7284994 : Nat := 118140960795 + 7284994 * 2 ^ 59
def prefixEnd_7284994 : Nat := 4983230072969 + 3 ^ 40 * 7284994 * 2
def baseEnd_7284994 : Nat := 3740703487120175661171929

theorem tailTrace_7284994 : CollatzResearch.WordTrace tailWord_7284994 prefixEnd_7284994 3740703487120175661171929 := by
  unfold tailWord_7284994
  simp only [CollatzResearch.WordTrace]
  refine ⟨66426389942429597691561509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177137039846478927177497357 66426389942429597691561509)
  ·
    refine ⟨12454948114205549567167783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66426389942429597691561509 12454948114205549567167783)
    ·
      refine ⟨18682422171308324350751675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12454948114205549567167783 18682422171308324350751675)
      ·
        refine ⟨28023633256962486526127513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18682422171308324350751675 28023633256962486526127513)
        ·
          refine ⟨21017724942721864894595635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28023633256962486526127513 21017724942721864894595635)
          ·
            refine ⟨31526587414082797341893453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21017724942721864894595635 31526587414082797341893453)
            ·
              refine ⟨11822470280281049003210045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31526587414082797341893453 11822470280281049003210045)
              ·
                refine ⟨4433426355105393376203767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11822470280281049003210045 4433426355105393376203767)
                ·
                  refine ⟨6650139532658090064305651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4433426355105393376203767 6650139532658090064305651)
                  ·
                    refine ⟨9975209298987135096458477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6650139532658090064305651 9975209298987135096458477)
                    ·
                      refine ⟨3740703487120175661171929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9975209298987135096458477 3740703487120175661171929)
                      ·
                        rfl

theorem cell23_7284994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7284994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7284994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7284994 prefixEnd_7284994 := by exact prefixLift 7284994
  have htrace : WordTrace (prefixWord ++ tailWord_7284994) baseStart_7284994 baseEnd_7284994 := by
    simpa [prefixWord, tailWord_7284994, baseEnd_7284994] using wordTrace_append hprefix tailTrace_7284994
  have hstable : (prefixWord ++ tailWord_7284994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7284994).length < 2 ^ (prefixWord ++ tailWord_7284994).sum := by decide
  have hdescent : baseEnd_7284994 < baseStart_7284994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7284994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285003 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 3]
def baseStart_7285003 : Nat := 118140960795 + 7285003 * 2 ^ 59
def prefixEnd_7285003 : Nat := 4983230072969 + 3 ^ 40 * 7285003 * 2
def baseEnd_7285003 : Nat := 3740708108446066125959387

theorem tailTrace_7285003 : CollatzResearch.WordTrace tailWord_7285003 prefixEnd_7285003 3740708108446066125959387 := by
  unfold tailWord_7285003
  simp only [CollatzResearch.WordTrace]
  refine ⟨265705888026685785303323663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177137258684457190202215775 265705888026685785303323663)
  ·
    refine ⟨398558832040028677954985495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265705888026685785303323663 398558832040028677954985495)
    ·
      refine ⟨597838248060043016932478243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398558832040028677954985495 597838248060043016932478243)
      ·
        refine ⟨896757372090064525398717365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597838248060043016932478243 896757372090064525398717365)
        ·
          refine ⟨84071003633443549256129753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 896757372090064525398717365 84071003633443549256129753)
          ·
            refine ⟨63053252725082661942097315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84071003633443549256129753 63053252725082661942097315)
            ·
              refine ⟨94579879087623992913145973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63053252725082661942097315 94579879087623992913145973)
              ·
                refine ⟨8866863664464749335607435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94579879087623992913145973 8866863664464749335607435)
                ·
                  refine ⟨13300295496697124003411153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8866863664464749335607435 13300295496697124003411153)
                  ·
                    refine ⟨9975221622522843002558365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13300295496697124003411153 9975221622522843002558365)
                    ·
                      refine ⟨3740708108446066125959387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9975221622522843002558365 3740708108446066125959387)
                      ·
                        rfl

theorem cell23_7285003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 3].length) (baseStart_7285003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285003 prefixEnd_7285003 := by exact prefixLift 7285003
  have htrace : WordTrace (prefixWord ++ tailWord_7285003) baseStart_7285003 baseEnd_7285003 := by
    simpa [prefixWord, tailWord_7285003, baseEnd_7285003] using wordTrace_append hprefix tailTrace_7285003
  have hstable : (prefixWord ++ tailWord_7285003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285003).length < 2 ^ (prefixWord ++ tailWord_7285003).sum := by decide
  have hdescent : baseEnd_7285003 < baseStart_7285003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285031 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7285031 : Nat := 118140960795 + 7285031 * 2 ^ 59
def prefixEnd_7285031 : Nat := 4983230072969 + 3 ^ 40 * 7285031 * 2
def baseEnd_7285031 : Nat := 1246907495301464005469753

theorem tailTrace_7285031 : CollatzResearch.WordTrace tailWord_7285031 prefixEnd_7285031 1246907495301464005469753 := by
  unfold tailWord_7285031
  simp only [CollatzResearch.WordTrace]
  refine ⟨265706909270584346085342947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177137939513722897390228631 265706909270584346085342947)
  ·
    refine ⟨398560363905876519128014421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265706909270584346085342947 398560363905876519128014421)
    ·
      refine ⟨4670629264521990458531419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 398560363905876519128014421 4670629264521990458531419)
      ·
        refine ⟨7005943896782985687797129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4670629264521990458531419 7005943896782985687797129)
        ·
          refine ⟨5254457922587239265847847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7005943896782985687797129 5254457922587239265847847)
          ·
            refine ⟨7881686883880858898771771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254457922587239265847847 7881686883880858898771771)
            ·
              refine ⟨11822530325821288348157657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881686883880858898771771 11822530325821288348157657)
              ·
                refine ⟨8866897744365966261118243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11822530325821288348157657 8866897744365966261118243)
                ·
                  refine ⟨13300346616548949391677365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8866897744365966261118243 13300346616548949391677365)
                  ·
                    refine ⟨1246907495301464005469753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13300346616548949391677365 1246907495301464005469753)
                    ·
                      rfl

theorem cell23_7285031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7285031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285031 prefixEnd_7285031 := by exact prefixLift 7285031
  have htrace : WordTrace (prefixWord ++ tailWord_7285031) baseStart_7285031 baseEnd_7285031 := by
    simpa [prefixWord, tailWord_7285031, baseEnd_7285031] using wordTrace_append hprefix tailTrace_7285031
  have hstable : (prefixWord ++ tailWord_7285031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285031).length < 2 ^ (prefixWord ++ tailWord_7285031).sum := by decide
  have hdescent : baseEnd_7285031 < baseStart_7285031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285034 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7285034 : Nat := 118140960795 + 7285034 * 2 ^ 59
def prefixEnd_7285034 : Nat := 4983230072969 + 3 ^ 40 * 7285034 * 2
def baseEnd_7285034 : Nat := 3740724026346355504671745

theorem tailTrace_7285034 : CollatzResearch.WordTrace tailWord_7285034 prefixEnd_7285034 3740724026346355504671745 := by
  unfold tailWord_7285034
  simp only [CollatzResearch.WordTrace]
  refine ⟨66426754672393369399425539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177138012459715651731801437 66426754672393369399425539)
  ·
    refine ⟨99640132008590054099138309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66426754672393369399425539 99640132008590054099138309)
    ·
      refine ⟨18682524751610635143588433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99640132008590054099138309 18682524751610635143588433)
      ·
        refine ⟨14011893563707976357691325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18682524751610635143588433 14011893563707976357691325)
        ·
          refine ⟨5254460086390491134134247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14011893563707976357691325 5254460086390491134134247)
          ·
            refine ⟨7881690129585736701201371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254460086390491134134247 7881690129585736701201371)
            ·
              refine ⟨11822535194378605051802057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881690129585736701201371 11822535194378605051802057)
              ·
                refine ⟨8866901395783953788851543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11822535194378605051802057 8866901395783953788851543)
                ·
                  refine ⟨13300352093675930683277315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8866901395783953788851543 13300352093675930683277315)
                  ·
                    refine ⟨19950528140513896024915973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13300352093675930683277315 19950528140513896024915973)
                    ·
                      refine ⟨3740724026346355504671745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19950528140513896024915973 3740724026346355504671745)
                      ·
                        rfl

theorem cell23_7285034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7285034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285034 prefixEnd_7285034 := by exact prefixLift 7285034
  have htrace : WordTrace (prefixWord ++ tailWord_7285034) baseStart_7285034 baseEnd_7285034 := by
    simpa [prefixWord, tailWord_7285034, baseEnd_7285034] using wordTrace_append hprefix tailTrace_7285034
  have hstable : (prefixWord ++ tailWord_7285034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285034).length < 2 ^ (prefixWord ++ tailWord_7285034).sum := by decide
  have hdescent : baseEnd_7285034 < baseStart_7285034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285037 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_7285037 : Nat := 118140960795 + 7285037 * 2 ^ 59
def prefixEnd_7285037 : Nat := 4983230072969 + 3 ^ 40 * 7285037 * 2
def baseEnd_7285037 : Nat := 3740725566788318992934231

theorem tailTrace_7285037 : CollatzResearch.WordTrace tailWord_7285037 prefixEnd_7285037 3740725566788318992934231 := by
  unfold tailWord_7285037
  simp only [CollatzResearch.WordTrace]
  refine ⟨265707128108562609110061365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177138085405708406073374243 265707128108562609110061365)
  ·
    refine ⟨24910043260177744604068253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265707128108562609110061365 24910043260177744604068253)
    ·
      refine ⟨9341266222566654226525595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24910043260177744604068253 9341266222566654226525595)
      ·
        refine ⟨14011899333849981339788393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9341266222566654226525595 14011899333849981339788393)
        ·
          refine ⟨10508924500387486004841295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14011899333849981339788393 10508924500387486004841295)
          ·
            refine ⟨15763386750581229007261943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10508924500387486004841295 15763386750581229007261943)
            ·
              refine ⟨23645080125871843510892915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15763386750581229007261943 23645080125871843510892915)
              ·
                refine ⟨35467620188807765266339373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23645080125871843510892915 35467620188807765266339373)
                ·
                  refine ⟨13300357570802911974877265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35467620188807765266339373 13300357570802911974877265)
                  ·
                    refine ⟨9975268178102183981157949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13300357570802911974877265 9975268178102183981157949)
                    ·
                      refine ⟨3740725566788318992934231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9975268178102183981157949 3740725566788318992934231)
                      ·
                        rfl

theorem cell23_7285037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_7285037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285037 prefixEnd_7285037 := by exact prefixLift 7285037
  have htrace : WordTrace (prefixWord ++ tailWord_7285037) baseStart_7285037 baseEnd_7285037 := by
    simpa [prefixWord, tailWord_7285037, baseEnd_7285037] using wordTrace_append hprefix tailTrace_7285037
  have hstable : (prefixWord ++ tailWord_7285037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285037).length < 2 ^ (prefixWord ++ tailWord_7285037).sum := by decide
  have hdescent : baseEnd_7285037 < baseStart_7285037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285160 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7285160 : Nat := 118140960795 + 7285160 * 2 ^ 59
def prefixEnd_7285160 : Nat := 4983230072969 + 3 ^ 40 * 7285160 * 2
def baseEnd_7285160 : Nat := 1246929574969607337232055

theorem tailTrace_7285160 : CollatzResearch.WordTrace tailWord_7285160 prefixEnd_7285160 1246929574969607337232055 := by
  unfold tailWord_7285160
  simp only [CollatzResearch.WordTrace]
  refine ⟨132855807143558500558394467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177141076191411334077859289 132855807143558500558394467)
  ·
    refine ⟨199283710715337750837591701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132855807143558500558394467 199283710715337750837591701)
    ·
      refine ⟨9341423939781457070512111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199283710715337750837591701 9341423939781457070512111)
      ·
        refine ⟨14012135909672185605768167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9341423939781457070512111 14012135909672185605768167)
        ·
          refine ⟨21018203864508278408652251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14012135909672185605768167 21018203864508278408652251)
          ·
            refine ⟨31527305796762417612978377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21018203864508278408652251 31527305796762417612978377)
            ·
              refine ⟨23645479347571813209733783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31527305796762417612978377 23645479347571813209733783)
              ·
                refine ⟨35468219021357719814600675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23645479347571813209733783 35468219021357719814600675)
                ·
                  refine ⟨53202328532036579721901013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35468219021357719814600675 53202328532036579721901013)
                  ·
                    refine ⟨1246929574969607337232055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53202328532036579721901013 1246929574969607337232055)
                    ·
                      rfl

theorem cell23_7285160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7285160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285160 prefixEnd_7285160 := by exact prefixLift 7285160
  have htrace : WordTrace (prefixWord ++ tailWord_7285160) baseStart_7285160 baseEnd_7285160 := by
    simpa [prefixWord, tailWord_7285160, baseEnd_7285160] using wordTrace_append hprefix tailTrace_7285160
  have hstable : (prefixWord ++ tailWord_7285160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285160).length < 2 ^ (prefixWord ++ tailWord_7285160).sum := by decide
  have hdescent : baseEnd_7285160 < baseStart_7285160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285180 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7285180 : Nat := 118140960795 + 7285180 * 2 ^ 59
def prefixEnd_7285180 : Nat := 4983230072969 + 3 ^ 40 * 7285180 * 2
def baseEnd_7285180 : Nat := 3740798994521911933446073

theorem tailTrace_7285180 : CollatzResearch.WordTrace tailWord_7285180 prefixEnd_7285180 3740798994521911933446073 := by
  unfold tailWord_7285180
  simp only [CollatzResearch.WordTrace]
  refine ⟨132856171873522272266258497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177141562498029696355011329 132856171873522272266258497)
  ·
    refine ⟨99642128905141704199693873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132856171873522272266258497 99642128905141704199693873)
    ·
      refine ⟨74731596678856278149770405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99642128905141704199693873 74731596678856278149770405)
      ·
        refine ⟨14012174377285552153081951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74731596678856278149770405 14012174377285552153081951)
        ·
          refine ⟨21018261565928328229622927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14012174377285552153081951 21018261565928328229622927)
          ·
            refine ⟨31527392348892492344434391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21018261565928328229622927 31527392348892492344434391)
            ·
              refine ⟨47291088523338738516651587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31527392348892492344434391 47291088523338738516651587)
              ·
                refine ⟨70936632785008107774977381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47291088523338738516651587 70936632785008107774977381)
                ·
                  refine ⟨13300618647189020207808259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70936632785008107774977381 13300618647189020207808259)
                  ·
                    refine ⟨19950927970783530311712389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13300618647189020207808259 19950927970783530311712389)
                    ·
                      refine ⟨3740798994521911933446073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19950927970783530311712389 3740798994521911933446073)
                      ·
                        rfl

theorem cell23_7285180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7285180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285180 prefixEnd_7285180 := by exact prefixLift 7285180
  have htrace : WordTrace (prefixWord ++ tailWord_7285180) baseStart_7285180 baseEnd_7285180 := by
    simpa [prefixWord, tailWord_7285180, baseEnd_7285180] using wordTrace_append hprefix tailTrace_7285180
  have hstable : (prefixWord ++ tailWord_7285180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285180).length < 2 ^ (prefixWord ++ tailWord_7285180).sum := by decide
  have hdescent : baseEnd_7285180 < baseStart_7285180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285263 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 1, 6]
def baseStart_7285263 : Nat := 118140960795 + 7285263 * 2 ^ 59
def prefixEnd_7285263 : Nat := 4983230072969 + 3 ^ 40 * 7285263 * 2
def baseEnd_7285263 : Nat := 1246947204472078369569397

theorem tailTrace_7285263 : CollatzResearch.WordTrace tailWord_7285263 prefixEnd_7285263 1246947204472078369569397 := by
  unfold tailWord_7285263
  simp only [CollatzResearch.WordTrace]
  refine ⟨265715371005743849707788443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177143580670495899805192295 265715371005743849707788443)
  ·
    refine ⟨398573056508615774561682665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265715371005743849707788443 398573056508615774561682665)
    ·
      refine ⟨298929792381461830921261999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398573056508615774561682665 298929792381461830921261999)
      ·
        refine ⟨448394688572192746381892999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298929792381461830921261999 448394688572192746381892999)
        ·
          refine ⟨672592032858289119572839499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448394688572192746381892999 672592032858289119572839499)
          ·
            refine ⟨1008888049287433679359259249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672592032858289119572839499 1008888049287433679359259249)
            ·
              refine ⟨756666036965575259519444437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008888049287433679359259249 756666036965575259519444437)
              ·
                refine ⟨17734360241380670144986979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 756666036965575259519444437 17734360241380670144986979)
                ·
                  refine ⟨26601540362071005217480469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17734360241380670144986979 26601540362071005217480469)
                  ·
                    refine ⟨1246947204472078369569397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26601540362071005217480469 1246947204472078369569397)
                    ·
                      rfl

theorem cell23_7285263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_7285263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285263 prefixEnd_7285263 := by exact prefixLift 7285263
  have htrace : WordTrace (prefixWord ++ tailWord_7285263) baseStart_7285263 baseEnd_7285263 := by
    simpa [prefixWord, tailWord_7285263, baseEnd_7285263] using wordTrace_append hprefix tailTrace_7285263
  have hstable : (prefixWord ++ tailWord_7285263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285263).length < 2 ^ (prefixWord ++ tailWord_7285263).sum := by decide
  have hdescent : baseEnd_7285263 < baseStart_7285263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285273 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_7285273 : Nat := 118140960795 + 7285273 * 2 ^ 59
def prefixEnd_7285273 : Nat := 4983230072969 + 3 ^ 40 * 7285273 * 2
def baseEnd_7285273 : Nat := 3740846748222780069583145

theorem tailTrace_7285273 : CollatzResearch.WordTrace tailWord_7285273 prefixEnd_7285273 3740846748222780069583145 := by
  unfold tailWord_7285273
  simp only [CollatzResearch.WordTrace]
  refine ⟨265715735735707621415652473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177143823823805080943768315 265715735735707621415652473)
  ·
    refine ⟨199286801801780716061739355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265715735735707621415652473 199286801801780716061739355)
    ·
      refine ⟨298930202702671074092609033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199286801801780716061739355 298930202702671074092609033)
      ·
        refine ⟨224197652027003305569456775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298930202702671074092609033 224197652027003305569456775)
        ·
          refine ⟨336296478040504958354185163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224197652027003305569456775 336296478040504958354185163)
          ·
            refine ⟨504444717060757437531277745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336296478040504958354185163 504444717060757437531277745)
            ·
              refine ⟨378333537795568078148458309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504444717060757437531277745 378333537795568078148458309)
              ·
                refine ⟨70937538336669014652835933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378333537795568078148458309 70937538336669014652835933)
                ·
                  refine ⟨26601576876250880494813475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70937538336669014652835933 26601576876250880494813475)
                  ·
                    refine ⟨39902365314376320742220213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26601576876250880494813475 39902365314376320742220213)
                    ·
                      refine ⟨3740846748222780069583145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39902365314376320742220213 3740846748222780069583145)
                      ·
                        rfl

theorem cell23_7285273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_7285273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285273 prefixEnd_7285273 := by exact prefixLift 7285273
  have htrace : WordTrace (prefixWord ++ tailWord_7285273) baseStart_7285273 baseEnd_7285273 := by
    simpa [prefixWord, tailWord_7285273, baseEnd_7285273] using wordTrace_append hprefix tailTrace_7285273
  have hstable : (prefixWord ++ tailWord_7285273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285273).length < 2 ^ (prefixWord ++ tailWord_7285273).sum := by decide
  have hdescent : baseEnd_7285273 < baseStart_7285273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285284 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_7285284 : Nat := 118140960795 + 7285284 * 2 ^ 59
def prefixEnd_7285284 : Nat := 4983230072969 + 3 ^ 40 * 7285284 * 2
def baseEnd_7285284 : Nat := 1246950798836659842181865

theorem tailTrace_7285284 : CollatzResearch.WordTrace tailWord_7285284 prefixEnd_7285284 1246950798836659842181865 := by
  unfold tailWord_7285284
  simp only [CollatzResearch.WordTrace]
  refine ⟨132858068469333885147151453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177144091292445180196201937 132858068469333885147151453)
  ·
    refine ⟨49821775676000206930181795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132858068469333885147151453 49821775676000206930181795)
    ·
      refine ⟨74732663514000310395272693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49821775676000206930181795 74732663514000310395272693)
      ·
        refine ⟨7006187204437529099556815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74732663514000310395272693 7006187204437529099556815)
        ·
          refine ⟨10509280806656293649335223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006187204437529099556815 10509280806656293649335223)
          ·
            refine ⟨15763921209984440474002835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10509280806656293649335223 15763921209984440474002835)
            ·
              refine ⟨23645881814976660711004253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15763921209984440474002835 23645881814976660711004253)
              ·
                refine ⟨8867205680616247766626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23645881814976660711004253 8867205680616247766626595)
                ·
                  refine ⟨13300808520924371649939893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8867205680616247766626595 13300808520924371649939893)
                  ·
                    refine ⟨1246950798836659842181865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13300808520924371649939893 1246950798836659842181865)
                    ·
                      rfl

theorem cell23_7285284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_7285284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285284 prefixEnd_7285284 := by exact prefixLift 7285284
  have htrace : WordTrace (prefixWord ++ tailWord_7285284) baseStart_7285284 baseEnd_7285284 := by
    simpa [prefixWord, tailWord_7285284, baseEnd_7285284] using wordTrace_append hprefix tailTrace_7285284
  have hstable : (prefixWord ++ tailWord_7285284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285284).length < 2 ^ (prefixWord ++ tailWord_7285284).sum := by decide
  have hdescent : baseEnd_7285284 < baseStart_7285284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285297 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 2, 4]
def baseStart_7285297 : Nat := 118140960795 + 7285297 * 2 ^ 59
def prefixEnd_7285297 : Nat := 4983230072969 + 3 ^ 40 * 7285297 * 2
def baseEnd_7285297 : Nat := 1246953023919495991894345

theorem tailTrace_7285297 : CollatzResearch.WordTrace tailWord_7285297 prefixEnd_7285297 1246953023919495991894345 := by
  unfold tailWord_7285297
  simp only [CollatzResearch.WordTrace]
  refine ⟨265716611087620673514526145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177144407391747115676350763 265716611087620673514526145)
  ·
    refine ⟨199287458315715505135894609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265716611087620673514526145 199287458315715505135894609)
    ·
      refine ⟨149465593736786628851920957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199287458315715505135894609 149465593736786628851920957)
      ·
        refine ⟨56049597651294985819470359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149465593736786628851920957 56049597651294985819470359)
        ·
          refine ⟨84074396476942478729205539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56049597651294985819470359 84074396476942478729205539)
          ·
            refine ⟨126111594715413718093808309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84074396476942478729205539 126111594715413718093808309)
            ·
              refine ⟨11822962004570036071294529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126111594715413718093808309 11822962004570036071294529)
              ·
                refine ⟨8867221503427527053470897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11822962004570036071294529 8867221503427527053470897)
                ·
                  refine ⟨6650416127570645290103173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8867221503427527053470897 6650416127570645290103173)
                  ·
                    refine ⟨1246953023919495991894345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6650416127570645290103173 1246953023919495991894345)
                    ·
                      rfl

theorem cell23_7285297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_7285297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285297 prefixEnd_7285297 := by exact prefixLift 7285297
  have htrace : WordTrace (prefixWord ++ tailWord_7285297) baseStart_7285297 baseEnd_7285297 := by
    simpa [prefixWord, tailWord_7285297, baseEnd_7285297] using wordTrace_append hprefix tailTrace_7285297
  have hstable : (prefixWord ++ tailWord_7285297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285297).length < 2 ^ (prefixWord ++ tailWord_7285297).sum := by decide
  have hdescent : baseEnd_7285297 < baseStart_7285297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285304 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 3, 2, 2]
def baseStart_7285304 : Nat := 118140960795 + 7285304 * 2 ^ 59
def prefixEnd_7285304 : Nat := 4983230072969 + 3 ^ 40 * 7285304 * 2
def baseEnd_7285304 : Nat := 3740862666123069448295503

theorem tailTrace_7285304 : CollatzResearch.WordTrace tailWord_7285304 prefixEnd_7285304 3740862666123069448295503 := by
  unfold tailWord_7285304
  simp only [CollatzResearch.WordTrace]
  refine ⟨132858433199297656855015483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177144577599063542473353977 132858433199297656855015483)
  ·
    refine ⟨199287649798946485282523225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132858433199297656855015483 199287649798946485282523225)
    ·
      refine ⟨149465737349209863961892419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199287649798946485282523225 149465737349209863961892419)
      ·
        refine ⟨224198606023814795942838629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149465737349209863961892419 224198606023814795942838629)
        ·
          refine ⟨42037238629465274239282243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224198606023814795942838629 42037238629465274239282243)
          ·
            refine ⟨63055857944197911358923365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42037238629465274239282243 63055857944197911358923365)
            ·
              refine ⟨11822973364537108379798131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63055857944197911358923365 11822973364537108379798131)
              ·
                refine ⟨17734460046805662569697197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11822973364537108379798131 17734460046805662569697197)
                ·
                  refine ⟨6650422517552123463636449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17734460046805662569697197 6650422517552123463636449)
                  ·
                    refine ⟨4987816888164092597727337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6650422517552123463636449 4987816888164092597727337)
                    ·
                      refine ⟨3740862666123069448295503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987816888164092597727337 3740862666123069448295503)
                      ·
                        rfl

theorem cell23_7285304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_7285304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285304 prefixEnd_7285304 := by exact prefixLift 7285304
  have htrace : WordTrace (prefixWord ++ tailWord_7285304) baseStart_7285304 baseEnd_7285304 := by
    simpa [prefixWord, tailWord_7285304, baseEnd_7285304] using wordTrace_append hprefix tailTrace_7285304
  have hstable : (prefixWord ++ tailWord_7285304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285304).length < 2 ^ (prefixWord ++ tailWord_7285304).sum := by decide
  have hdescent : baseEnd_7285304 < baseStart_7285304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285317 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_7285317 : Nat := 118140960795 + 7285317 * 2 ^ 59
def prefixEnd_7285317 : Nat := 4983230072969 + 3 ^ 40 * 7285317 * 2
def baseEnd_7285317 : Nat := 3740869341371577897432943

theorem tailTrace_7285317 : CollatzResearch.WordTrace tailWord_7285317 prefixEnd_7285317 3740869341371577897432943 := by
  unfold tailWord_7285317
  simp only [CollatzResearch.WordTrace]
  refine ⟨265717340547548216930254205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177144893698365477953502803 265717340547548216930254205)
  ·
    refine ⟨99644002705330581348845327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265717340547548216930254205 99644002705330581348845327)
    ·
      refine ⟨149466004057995872023267991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99644002705330581348845327 149466004057995872023267991)
      ·
        refine ⟨224199006086993808034901987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149466004057995872023267991 224199006086993808034901987)
        ·
          refine ⟨336298509130490712052352981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224199006086993808034901987 336298509130490712052352981)
          ·
            refine ⟨7881996307745876063727023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 336298509130490712052352981 7881996307745876063727023)
            ·
              refine ⟨11822994461618814095590535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881996307745876063727023 11822994461618814095590535)
              ·
                refine ⟨17734491692428221143385803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11822994461618814095590535 17734491692428221143385803)
                ·
                  refine ⟨26601737538642331715078705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17734491692428221143385803 26601737538642331715078705)
                  ·
                    refine ⟨19951303153981748786309029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26601737538642331715078705 19951303153981748786309029)
                    ·
                      refine ⟨3740869341371577897432943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19951303153981748786309029 3740869341371577897432943)
                      ·
                        rfl

theorem cell23_7285317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_7285317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285317 prefixEnd_7285317 := by exact prefixLift 7285317
  have htrace : WordTrace (prefixWord ++ tailWord_7285317) baseStart_7285317 baseEnd_7285317 := by
    simpa [prefixWord, tailWord_7285317, baseEnd_7285317] using wordTrace_append hprefix tailTrace_7285317
  have hstable : (prefixWord ++ tailWord_7285317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285317).length < 2 ^ (prefixWord ++ tailWord_7285317).sum := by decide
  have hdescent : baseEnd_7285317 < baseStart_7285317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285323 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 2, 7]
def baseStart_7285323 : Nat := 118140960795 + 7285323 * 2 ^ 59
def prefixEnd_7285323 : Nat := 4983230072969 + 3 ^ 40 * 7285323 * 2
def baseEnd_7285323 : Nat := 1246957474085168291319305

theorem tailTrace_7285323 : CollatzResearch.WordTrace tailWord_7285323 prefixEnd_7285323 1246957474085168291319305 := by
  unfold tailWord_7285323
  simp only [CollatzResearch.WordTrace]
  refine ⟨265717559385526479954972623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177145039590350986636648415 265717559385526479954972623)
  ·
    refine ⟨398576339078289719932458935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265717559385526479954972623 398576339078289719932458935)
    ·
      refine ⟨597864508617434579898688403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398576339078289719932458935 597864508617434579898688403)
      ·
        refine ⟨896796762926151869848032605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597864508617434579898688403 896796762926151869848032605)
        ·
          refine ⟨336298786097306951193012227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 896796762926151869848032605 336298786097306951193012227)
          ·
            refine ⟨504448179145960426789518341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336298786097306951193012227 504448179145960426789518341)
            ·
              refine ⟨94584033589867580023034689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 504448179145960426789518341 94584033589867580023034689)
              ·
                refine ⟨70938025192400685017276017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94584033589867580023034689 70938025192400685017276017)
                ·
                  refine ⟨53203518894300513762957013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70938025192400685017276017 53203518894300513762957013)
                  ·
                    refine ⟨1246957474085168291319305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53203518894300513762957013 1246957474085168291319305)
                    ·
                      rfl

theorem cell23_7285323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_7285323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285323 prefixEnd_7285323 := by exact prefixLift 7285323
  have htrace : WordTrace (prefixWord ++ tailWord_7285323) baseStart_7285323 baseEnd_7285323 := by
    simpa [prefixWord, tailWord_7285323, baseEnd_7285323] using wordTrace_append hprefix tailTrace_7285323
  have hstable : (prefixWord ++ tailWord_7285323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285323).length < 2 ^ (prefixWord ++ tailWord_7285323).sum := by decide
  have hdescent : baseEnd_7285323 < baseStart_7285323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285343 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_7285343 : Nat := 118140960795 + 7285343 * 2 ^ 59
def prefixEnd_7285343 : Nat := 4983230072969 + 3 ^ 40 * 7285343 * 2
def baseEnd_7285343 : Nat := 3740882691868594795707823

theorem tailTrace_7285343 : CollatzResearch.WordTrace tailWord_7285343 prefixEnd_7285343 3740882691868594795707823 := by
  unfold tailWord_7285343
  simp only [CollatzResearch.WordTrace]
  refine ⟨265718288845454023370700683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177145525896969348913800455 265718288845454023370700683)
  ·
    refine ⟨398577433268181035056051025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265718288845454023370700683 398577433268181035056051025)
    ·
      refine ⟨298933074951135776292038269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398577433268181035056051025 298933074951135776292038269)
      ·
        refine ⟨112099903106675916109514351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298933074951135776292038269 112099903106675916109514351)
        ·
          refine ⟨168149854660013874164271527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112099903106675916109514351 168149854660013874164271527)
          ·
            refine ⟨252224781990020811246407291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168149854660013874164271527 252224781990020811246407291)
            ·
              refine ⟨378337172985031216869610937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252224781990020811246407291 378337172985031216869610937)
              ·
                refine ⟨283752879738773412652208203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378337172985031216869610937 283752879738773412652208203)
                ·
                  refine ⟨425629319608160118978312305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283752879738773412652208203 425629319608160118978312305)
                  ·
                    refine ⟨319221989706120089233734229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 425629319608160118978312305 319221989706120089233734229)
                    ·
                      refine ⟨3740882691868594795707823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319221989706120089233734229 3740882691868594795707823)
                      ·
                        rfl

theorem cell23_7285343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_7285343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285343 prefixEnd_7285343 := by exact prefixLift 7285343
  have htrace : WordTrace (prefixWord ++ tailWord_7285343) baseStart_7285343 baseEnd_7285343 := by
    simpa [prefixWord, tailWord_7285343, baseEnd_7285343] using wordTrace_append hprefix tailTrace_7285343
  have hstable : (prefixWord ++ tailWord_7285343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285343).length < 2 ^ (prefixWord ++ tailWord_7285343).sum := by decide
  have hdescent : baseEnd_7285343 < baseStart_7285343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285354 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_7285354 : Nat := 118140960795 + 7285354 * 2 ^ 59
def prefixEnd_7285354 : Nat := 4983230072969 + 3 ^ 40 * 7285354 * 2
def baseEnd_7285354 : Nat := 3740888340155794252670273

theorem tailTrace_7285354 : CollatzResearch.WordTrace tailWord_7285354 prefixEnd_7285354 3740888340155794252670273 := by
  unfold tailWord_7285354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66429672512103543062337779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177145793365609448166234077 66429672512103543062337779)
  ·
    refine ⟨99644508768155314593506669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66429672512103543062337779 99644508768155314593506669)
    ·
      refine ⟨37366690788058242972565001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99644508768155314593506669 37366690788058242972565001)
      ·
        refine ⟨28025018091043682229423751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37366690788058242972565001 28025018091043682229423751)
        ·
          refine ⟨42037527136565523344135627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28025018091043682229423751 42037527136565523344135627)
          ·
            refine ⟨63056290704848285016203441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42037527136565523344135627 63056290704848285016203441)
            ·
              refine ⟨47292218028636213762152581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63056290704848285016203441 47292218028636213762152581)
              ·
                refine ⟨8867290880369290080403609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47292218028636213762152581 8867290880369290080403609)
                ·
                  refine ⟨6650468160276967560302707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8867290880369290080403609 6650468160276967560302707)
                  ·
                    refine ⟨9975702240415451340454061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6650468160276967560302707 9975702240415451340454061)
                    ·
                      refine ⟨3740888340155794252670273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9975702240415451340454061 3740888340155794252670273)
                      ·
                        rfl

theorem cell23_7285354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_7285354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285354 prefixEnd_7285354 := by exact prefixLift 7285354
  have htrace : WordTrace (prefixWord ++ tailWord_7285354) baseStart_7285354 baseEnd_7285354 := by
    simpa [prefixWord, tailWord_7285354, baseEnd_7285354] using wordTrace_append hprefix tailTrace_7285354
  have hstable : (prefixWord ++ tailWord_7285354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285354).length < 2 ^ (prefixWord ++ tailWord_7285354).sum := by decide
  have hdescent : baseEnd_7285354 < baseStart_7285354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285381 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 1, 3, 2]
def baseStart_7285381 : Nat := 118140960795 + 7285381 * 2 ^ 59
def prefixEnd_7285381 : Nat := 4983230072969 + 3 ^ 40 * 7285381 * 2
def baseEnd_7285381 : Nat := 3740902204133465647032649

theorem tailTrace_7285381 : CollatzResearch.WordTrace tailWord_7285381 prefixEnd_7285381 3740902204133465647032649 := by
  unfold tailWord_7285381
  simp only [CollatzResearch.WordTrace]
  refine ⟨265719674819316355860583997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177146449879544237240389331 265719674819316355860583997)
  ·
    refine ⟨99644878057243633447718999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265719674819316355860583997 99644878057243633447718999)
    ·
      refine ⟨149467317085865450171578499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99644878057243633447718999 149467317085865450171578499)
      ·
        refine ⟨224200975628798175257367749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149467317085865450171578499 224200975628798175257367749)
        ·
          refine ⟨42037682930399657860756453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224200975628798175257367749 42037682930399657860756453)
          ·
            refine ⟨7882065549449935848891835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42037682930399657860756453 7882065549449935848891835)
            ·
              refine ⟨11823098324174903773337753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7882065549449935848891835 11823098324174903773337753)
              ·
                refine ⟨8867323743131177830003315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11823098324174903773337753 8867323743131177830003315)
                ·
                  refine ⟨13300985614696766745004973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8867323743131177830003315 13300985614696766745004973)
                  ·
                    refine ⟨4987869605511287529376865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13300985614696766745004973 4987869605511287529376865)
                    ·
                      refine ⟨3740902204133465647032649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987869605511287529376865 3740902204133465647032649)
                      ·
                        rfl

theorem cell23_7285381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_7285381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285381 prefixEnd_7285381 := by exact prefixLift 7285381
  have htrace : WordTrace (prefixWord ++ tailWord_7285381) baseStart_7285381 baseEnd_7285381 := by
    simpa [prefixWord, tailWord_7285381, baseEnd_7285381] using wordTrace_append hprefix tailTrace_7285381
  have hstable : (prefixWord ++ tailWord_7285381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285381).length < 2 ^ (prefixWord ++ tailWord_7285381).sum := by decide
  have hdescent : baseEnd_7285381 < baseStart_7285381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285394 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_7285394 : Nat := 118140960795 + 7285394 * 2 ^ 59
def prefixEnd_7285394 : Nat := 4983230072969 + 3 ^ 40 * 7285394 * 2
def baseEnd_7285394 : Nat := 3740908879381974096170089

theorem tailTrace_7285394 : CollatzResearch.WordTrace tailWord_7285394 prefixEnd_7285394 3740908879381974096170089 := by
  unfold tailWord_7285394
  simp only [CollatzResearch.WordTrace]
  refine ⟨66430037242067314770201809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177146765978846172720538157 66430037242067314770201809)
  ·
    refine ⟨49822527931550486077651357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66430037242067314770201809 49822527931550486077651357)
    ·
      refine ⟨18683447974331432279119259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49822527931550486077651357 18683447974331432279119259)
      ·
        refine ⟨28025171961497148418678889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18683447974331432279119259 28025171961497148418678889)
        ·
          refine ⟨21018878971122861314009167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28025171961497148418678889 21018878971122861314009167)
          ·
            refine ⟨31528318456684291971013751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21018878971122861314009167 31528318456684291971013751)
            ·
              refine ⟨47292477685026437956520627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31528318456684291971013751 47292477685026437956520627)
              ·
                refine ⟨70938716527539656934780941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47292477685026437956520627 70938716527539656934780941)
                ·
                  refine ⟨26602018697827371350542853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70938716527539656934780941 26602018697827371350542853)
                  ·
                    refine ⟨4987878505842632128226785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26602018697827371350542853 4987878505842632128226785)
                    ·
                      refine ⟨3740908879381974096170089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4987878505842632128226785 3740908879381974096170089)
                      ·
                        rfl

theorem cell23_7285394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_7285394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285394 prefixEnd_7285394 := by exact prefixLift 7285394
  have htrace : WordTrace (prefixWord ++ tailWord_7285394) baseStart_7285394 baseEnd_7285394 := by
    simpa [prefixWord, tailWord_7285394, baseEnd_7285394] using wordTrace_append hprefix tailTrace_7285394
  have hstable : (prefixWord ++ tailWord_7285394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285394).length < 2 ^ (prefixWord ++ tailWord_7285394).sum := by decide
  have hdescent : baseEnd_7285394 < baseStart_7285394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285427 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 3]
def baseStart_7285427 : Nat := 118140960795 + 7285427 * 2 ^ 59
def prefixEnd_7285427 : Nat := 4983230072969 + 3 ^ 40 * 7285427 * 2
def baseEnd_7285427 : Nat := 3740925824243572467057437

theorem tailTrace_7285427 : CollatzResearch.WordTrace tailWord_7285427 prefixEnd_7285427 3740925824243572467057437 := by
  unfold tailWord_7285427
  simp only [CollatzResearch.WordTrace]
  refine ⟨265721352577149705716758535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177147568384766470477839023 265721352577149705716758535)
  ·
    refine ⟨398582028865724558575137803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265721352577149705716758535 398582028865724558575137803)
    ·
      refine ⟨597873043298586837862706705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398582028865724558575137803 597873043298586837862706705)
      ·
        refine ⟨448404782473940128397030029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597873043298586837862706705 448404782473940128397030029)
        ·
          refine ⟨168151793427727548148886261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448404782473940128397030029 168151793427727548148886261)
          ·
            refine ⟨15764230633849457638958087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168151793427727548148886261 15764230633849457638958087)
            ·
              refine ⟨23646345950774186458437131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15764230633849457638958087 23646345950774186458437131)
              ·
                refine ⟨35469518926161279687655697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23646345950774186458437131 35469518926161279687655697)
                ·
                  refine ⟨26602139194620959765741773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35469518926161279687655697 26602139194620959765741773)
                  ·
                    refine ⟨9975802197982859912153165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26602139194620959765741773 9975802197982859912153165)
                    ·
                      refine ⟨3740925824243572467057437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9975802197982859912153165 3740925824243572467057437)
                      ·
                        rfl

theorem cell23_7285427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_7285427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285427 prefixEnd_7285427 := by exact prefixLift 7285427
  have htrace : WordTrace (prefixWord ++ tailWord_7285427) baseStart_7285427 baseEnd_7285427 := by
    simpa [prefixWord, tailWord_7285427, baseEnd_7285427] using wordTrace_append hprefix tailTrace_7285427
  have hstable : (prefixWord ++ tailWord_7285427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285427).length < 2 ^ (prefixWord ++ tailWord_7285427).sum := by decide
  have hdescent : baseEnd_7285427 < baseStart_7285427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285487 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_7285487 : Nat := 118140960795 + 7285487 * 2 ^ 59
def prefixEnd_7285487 : Nat := 4983230072969 + 3 ^ 40 * 7285487 * 2
def baseEnd_7285487 : Nat := 3740956633082842232307161

theorem tailTrace_7285487 : CollatzResearch.WordTrace tailWord_7285487 prefixEnd_7285487 3740956633082842232307161 := by
  unfold tailWord_7285487
  simp only [CollatzResearch.WordTrace]
  refine ⟨265723540956932335963942715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177149027304621557309295143 265723540956932335963942715)
  ·
    refine ⟨398585311435398503945914073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265723540956932335963942715 398585311435398503945914073)
    ·
      refine ⟨298938983576548877959435555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398585311435398503945914073 298938983576548877959435555)
      ·
        refine ⟨448408475364823316939153333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298938983576548877959435555 448408475364823316939153333)
        ·
          refine ⟨42038294565452185963045625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 448408475364823316939153333 42038294565452185963045625)
          ·
            refine ⟨31528720924089139472284219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42038294565452185963045625 31528720924089139472284219)
            ·
              refine ⟨47293081386133709208426329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31528720924089139472284219 47293081386133709208426329)
              ·
                refine ⟨35469811039600281906319747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47293081386133709208426329 35469811039600281906319747)
                ·
                  refine ⟨53204716559400422859479621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35469811039600281906319747 53204716559400422859479621)
                  ·
                    refine ⟨9975884354887579286152429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53204716559400422859479621 9975884354887579286152429)
                    ·
                      refine ⟨3740956633082842232307161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9975884354887579286152429 3740956633082842232307161)
                      ·
                        rfl

theorem cell23_7285487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_7285487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285487 prefixEnd_7285487 := by exact prefixLift 7285487
  have htrace : WordTrace (prefixWord ++ tailWord_7285487) baseStart_7285487 baseEnd_7285487 := by
    simpa [prefixWord, tailWord_7285487, baseEnd_7285487] using wordTrace_append hprefix tailTrace_7285487
  have hstable : (prefixWord ++ tailWord_7285487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285487).length < 2 ^ (prefixWord ++ tailWord_7285487).sum := by decide
  have hdescent : baseEnd_7285487 < baseStart_7285487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285494 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_7285494 : Nat := 118140960795 + 7285494 * 2 ^ 59
def prefixEnd_7285494 : Nat := 4983230072969 + 3 ^ 40 * 7285494 * 2
def baseEnd_7285494 : Nat := 1246986742482474568306543

theorem tailTrace_7285494 : CollatzResearch.WordTrace tailWord_7285494 prefixEnd_7285494 1246986742482474568306543 := by
  unfold tailWord_7285494
  simp only [CollatzResearch.WordTrace]
  refine ⟨16607737266744186009965471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177149197511937984106298357 16607737266744186009965471)
  ·
    refine ⟨24911605900116279014948207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16607737266744186009965471 24911605900116279014948207)
    ·
      refine ⟨37367408850174418522422311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24911605900116279014948207 37367408850174418522422311)
      ·
        refine ⟨56051113275261627783633467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37367408850174418522422311 56051113275261627783633467)
        ·
          refine ⟨84076669912892441675450201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56051113275261627783633467 84076669912892441675450201)
          ·
            refine ⟨63057502434669331256587651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84076669912892441675450201 63057502434669331256587651)
            ·
              refine ⟨94586253652003996884881477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63057502434669331256587651 94586253652003996884881477)
              ·
                refine ⟨17734922559750749415915277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94586253652003996884881477 17734922559750749415915277)
                ·
                  refine ⟨6650595959906531030968229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17734922559750749415915277 6650595959906531030968229)
                  ·
                    refine ⟨1246986742482474568306543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6650595959906531030968229 1246986742482474568306543)
                    ·
                      rfl

theorem cell23_7285494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_7285494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285494 prefixEnd_7285494 := by exact prefixLift 7285494
  have htrace : WordTrace (prefixWord ++ tailWord_7285494) baseStart_7285494 baseEnd_7285494 := by
    simpa [prefixWord, tailWord_7285494, baseEnd_7285494] using wordTrace_append hprefix tailTrace_7285494
  have hstable : (prefixWord ++ tailWord_7285494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285494).length < 2 ^ (prefixWord ++ tailWord_7285494).sum := by decide
  have hdescent : baseEnd_7285494 < baseStart_7285494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285537 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_7285537 : Nat := 118140960795 + 7285537 * 2 ^ 59
def prefixEnd_7285537 : Nat := 4983230072969 + 3 ^ 40 * 7285537 * 2
def baseEnd_7285537 : Nat := 1246994102371855678893977

theorem tailTrace_7285537 : CollatzResearch.WordTrace tailWord_7285537 prefixEnd_7285537 1246994102371855678893977 := by
  unfold tailWord_7285537
  simp only [CollatzResearch.WordTrace]
  refine ⟨265725364606751194503262865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177150243071167463002175243 265725364606751194503262865)
  ·
    refine ⟨199294023455063395877447149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265725364606751194503262865 199294023455063395877447149)
    ·
      refine ⟨74735258795648773454042681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199294023455063395877447149 74735258795648773454042681)
      ·
        refine ⟨56051444096736580090532011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74735258795648773454042681 56051444096736580090532011)
        ·
          refine ⟨84077166145104870135798017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56051444096736580090532011 84077166145104870135798017)
          ·
            refine ⟨63057874608828652601848513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84077166145104870135798017 63057874608828652601848513)
            ·
              refine ⟨47293405956621489451386385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63057874608828652601848513 47293405956621489451386385)
              ·
                refine ⟨35470054467466117088539789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47293405956621489451386385 35470054467466117088539789)
                ·
                  refine ⟨13301270425299793908202421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35470054467466117088539789 13301270425299793908202421)
                  ·
                    refine ⟨1246994102371855678893977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13301270425299793908202421 1246994102371855678893977)
                    ·
                      rfl

theorem cell23_7285537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_7285537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285537 prefixEnd_7285537 := by exact prefixLift 7285537
  have htrace : WordTrace (prefixWord ++ tailWord_7285537) baseStart_7285537 baseEnd_7285537 := by
    simpa [prefixWord, tailWord_7285537, baseEnd_7285537] using wordTrace_append hprefix tailTrace_7285537
  have hstable : (prefixWord ++ tailWord_7285537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285537).length < 2 ^ (prefixWord ++ tailWord_7285537).sum := by decide
  have hdescent : baseEnd_7285537 < baseStart_7285537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285567 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 3, 6]
def baseStart_7285567 : Nat := 118140960795 + 7285567 * 2 ^ 59
def prefixEnd_7285567 : Nat := 4983230072969 + 3 ^ 40 * 7285567 * 2
def baseEnd_7285567 : Nat := 1246999237178400639768931

theorem tailTrace_7285567 : CollatzResearch.WordTrace tailWord_7285567 prefixEnd_7285567 1246999237178400639768931 := by
  unfold tailWord_7285567
  simp only [CollatzResearch.WordTrace]
  refine ⟨265726458796642509626854955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177150972531095006417903303 265726458796642509626854955)
  ·
    refine ⟨398589688194963764440282433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265726458796642509626854955 398589688194963764440282433)
    ·
      refine ⟨298942266146222823330211825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398589688194963764440282433 298942266146222823330211825)
      ·
        refine ⟨224206699609667117497658869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298942266146222823330211825 224206699609667117497658869)
        ·
          refine ⟨21019378088406292265405519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224206699609667117497658869 21019378088406292265405519)
          ·
            refine ⟨31529067132609438398108279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21019378088406292265405519 31529067132609438398108279)
            ·
              refine ⟨47293600698914157597162419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31529067132609438398108279 47293600698914157597162419)
              ·
                refine ⟨70940401048371236395743629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47293600698914157597162419 70940401048371236395743629)
                ·
                  refine ⟨26602650393139213648403861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70940401048371236395743629 26602650393139213648403861)
                  ·
                    refine ⟨1246999237178400639768931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26602650393139213648403861 1246999237178400639768931)
                    ·
                      rfl

theorem cell23_7285567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_7285567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285567 prefixEnd_7285567 := by exact prefixLift 7285567
  have htrace : WordTrace (prefixWord ++ tailWord_7285567) baseStart_7285567 baseEnd_7285567 := by
    simpa [prefixWord, tailWord_7285567, baseEnd_7285567] using wordTrace_append hprefix tailTrace_7285567
  have hstable : (prefixWord ++ tailWord_7285567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285567).length < 2 ^ (prefixWord ++ tailWord_7285567).sum := by decide
  have hdescent : baseEnd_7285567 < baseStart_7285567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285584 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 2, 4]
def baseStart_7285584 : Nat := 118140960795 + 7285584 * 2 ^ 59
def prefixEnd_7285584 : Nat := 4983230072969 + 3 ^ 40 * 7285584 * 2
def baseEnd_7285584 : Nat := 1247002146902109450931405

theorem tailTrace_7285584 : CollatzResearch.WordTrace tailWord_7285584 prefixEnd_7285584 1247002146902109450931405 := by
  unfold tailWord_7285584
  simp only [CollatzResearch.WordTrace]
  refine ⟨132863539418790460765111903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177151385891720614353482537 132863539418790460765111903)
  ·
    refine ⟨199295309128185691147667855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132863539418790460765111903 199295309128185691147667855)
    ·
      refine ⟨298942963692278536721501783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199295309128185691147667855 298942963692278536721501783)
      ·
        refine ⟨448414445538417805082252675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298942963692278536721501783 448414445538417805082252675)
        ·
          refine ⟨672621668307626707623379013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448414445538417805082252675 672621668307626707623379013)
          ·
            refine ⟨126116562807680007679383565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 672621668307626707623379013 126116562807680007679383565)
            ·
              refine ⟨47293711052880002879768837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126116562807680007679383565 47293711052880002879768837)
              ·
                refine ⟨8867570822415000539956657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47293711052880002879768837 8867570822415000539956657)
                ·
                  refine ⟨6650678116811250404967493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8867570822415000539956657 6650678116811250404967493)
                  ·
                    refine ⟨1247002146902109450931405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6650678116811250404967493 1247002146902109450931405)
                    ·
                      rfl

theorem cell23_7285584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_7285584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285584 prefixEnd_7285584 := by exact prefixLift 7285584
  have htrace : WordTrace (prefixWord ++ tailWord_7285584) baseStart_7285584 baseEnd_7285584 := by
    simpa [prefixWord, tailWord_7285584, baseEnd_7285584] using wordTrace_append hprefix tailTrace_7285584
  have hstable : (prefixWord ++ tailWord_7285584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285584).length < 2 ^ (prefixWord ++ tailWord_7285584).sum := by decide
  have hdescent : baseEnd_7285584 < baseStart_7285584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285594 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_7285594 : Nat := 118140960795 + 7285594 * 2 ^ 59
def prefixEnd_7285594 : Nat := 4983230072969 + 3 ^ 40 * 7285594 * 2
def baseEnd_7285594 : Nat := 3741011575512873313669169

theorem tailTrace_7285594 : CollatzResearch.WordTrace tailWord_7285594 prefixEnd_7285594 3741011575512873313669169 := by
  unfold tailWord_7285594
  simp only [CollatzResearch.WordTrace]
  refine ⟨66431860891886173309521959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177151629045029795492058557 66431860891886173309521959)
  ·
    refine ⟨99647791337829259964282939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66431860891886173309521959 99647791337829259964282939)
    ·
      refine ⟨149471687006743889946424409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99647791337829259964282939 149471687006743889946424409)
      ·
        refine ⟨112103765255057917459818307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149471687006743889946424409 112103765255057917459818307)
        ·
          refine ⟨168155647882586876189727461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112103765255057917459818307 168155647882586876189727461)
          ·
            refine ⟨31529183977985039285573899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168155647882586876189727461 31529183977985039285573899)
            ·
              refine ⟨47293775966977558928360849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31529183977985039285573899 47293775966977558928360849)
              ·
                refine ⟨35470331975233169196270637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47293775966977558928360849 35470331975233169196270637)
                ·
                  refine ⟨13301374490712438448601489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35470331975233169196270637 13301374490712438448601489)
                  ·
                    refine ⟨9976030868034328836451117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13301374490712438448601489 9976030868034328836451117)
                    ·
                      refine ⟨3741011575512873313669169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976030868034328836451117 3741011575512873313669169)
                      ·
                        rfl

theorem cell23_7285594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_7285594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285594 prefixEnd_7285594 := by exact prefixLift 7285594
  have htrace : WordTrace (prefixWord ++ tailWord_7285594) baseStart_7285594 baseEnd_7285594 := by
    simpa [prefixWord, tailWord_7285594, baseEnd_7285594] using wordTrace_append hprefix tailTrace_7285594
  have hstable : (prefixWord ++ tailWord_7285594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285594).length < 2 ^ (prefixWord ++ tailWord_7285594).sum := by decide
  have hdescent : baseEnd_7285594 < baseStart_7285594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285604 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_7285604 : Nat := 118140960795 + 7285604 * 2 ^ 59
def prefixEnd_7285604 : Nat := 4983230072969 + 3 ^ 40 * 7285604 * 2
def baseEnd_7285604 : Nat := 3741016710319418274544123

theorem tailTrace_7285604 : CollatzResearch.WordTrace tailWord_7285604 prefixEnd_7285604 3741016710319418274544123 := by
  unfold tailWord_7285604
  simp only [CollatzResearch.WordTrace]
  refine ⟨132863904148754232472975933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177151872198338976630634577 132863904148754232472975933)
  ·
    refine ⟨49823964055782837177365975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132863904148754232472975933 49823964055782837177365975)
    ·
      refine ⟨74735946083674255766048963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49823964055782837177365975 74735946083674255766048963)
      ·
        refine ⟨112103919125511383649073445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74735946083674255766048963 112103919125511383649073445)
        ·
          refine ⟨21019484836033384434201271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112103919125511383649073445 21019484836033384434201271)
          ·
            refine ⟨31529227254050076651301907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21019484836033384434201271 31529227254050076651301907)
            ·
              refine ⟨47293840881075114976952861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31529227254050076651301907 47293840881075114976952861)
              ·
                refine ⟨17735190330403168116357323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47293840881075114976952861 17735190330403168116357323)
                ·
                  refine ⟨26602785495604752174535985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17735190330403168116357323 26602785495604752174535985)
                  ·
                    refine ⟨19952089121703564130901989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26602785495604752174535985 19952089121703564130901989)
                    ·
                      refine ⟨3741016710319418274544123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19952089121703564130901989 3741016710319418274544123)
                      ·
                        rfl

theorem cell23_7285604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_7285604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285604 prefixEnd_7285604 := by exact prefixLift 7285604
  have htrace : WordTrace (prefixWord ++ tailWord_7285604) baseStart_7285604 baseEnd_7285604 := by
    simpa [prefixWord, tailWord_7285604, baseEnd_7285604] using wordTrace_append hprefix tailTrace_7285604
  have hstable : (prefixWord ++ tailWord_7285604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285604).length < 2 ^ (prefixWord ++ tailWord_7285604).sum := by decide
  have hdescent : baseEnd_7285604 < baseStart_7285604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285608 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_7285608 : Nat := 118140960795 + 7285608 * 2 ^ 59
def prefixEnd_7285608 : Nat := 4983230072969 + 3 ^ 40 * 7285608 * 2
def baseEnd_7285608 : Nat := 3741018764242036258894105

theorem tailTrace_7285608 : CollatzResearch.WordTrace tailWord_7285608 prefixEnd_7285608 3741018764242036258894105 := by
  unfold tailWord_7285608
  simp only [CollatzResearch.WordTrace]
  refine ⟨132863977094746986814548739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177151969459662649086064985 132863977094746986814548739)
  ·
    refine ⟨199295965642120480221823109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132863977094746986814548739 199295965642120480221823109)
    ·
      refine ⟨37367993557897590041591833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199295965642120480221823109 37367993557897590041591833)
      ·
        refine ⟨28025995168423192531193875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37367993557897590041591833 28025995168423192531193875)
        ·
          refine ⟨42038992752634788796790813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28025995168423192531193875 42038992752634788796790813)
          ·
            refine ⟨15764622282238045798796555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42038992752634788796790813 15764622282238045798796555)
            ·
              refine ⟨23646933423357068698194833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15764622282238045798796555 23646933423357068698194833)
              ·
                refine ⟨17735200067517801523646125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23646933423357068698194833 17735200067517801523646125)
                ·
                  refine ⟨6650700025319175571367297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17735200067517801523646125 6650700025319175571367297)
                  ·
                    refine ⟨4988025018989381678525473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6650700025319175571367297 4988025018989381678525473)
                    ·
                      refine ⟨3741018764242036258894105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988025018989381678525473 3741018764242036258894105)
                      ·
                        rfl

theorem cell23_7285608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_7285608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285608 prefixEnd_7285608 := by exact prefixLift 7285608
  have htrace : WordTrace (prefixWord ++ tailWord_7285608) baseStart_7285608 baseEnd_7285608 := by
    simpa [prefixWord, tailWord_7285608, baseEnd_7285608] using wordTrace_append hprefix tailTrace_7285608
  have hstable : (prefixWord ++ tailWord_7285608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285608).length < 2 ^ (prefixWord ++ tailWord_7285608).sum := by decide
  have hdescent : baseEnd_7285608 < baseStart_7285608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285625 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 1, 2, 2]
def baseStart_7285625 : Nat := 118140960795 + 7285625 * 2 ^ 59
def prefixEnd_7285625 : Nat := 4983230072969 + 3 ^ 40 * 7285625 * 2
def baseEnd_7285625 : Nat := 3741027493413162692381527

theorem tailTrace_7285625 : CollatzResearch.WordTrace tailWord_7285625 prefixEnd_7285625 3741027493413162692381527 := by
  unfold tailWord_7285625
  simp only [CollatzResearch.WordTrace]
  refine ⟨265728574230432385532466329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177152382820288257021644219 265728574230432385532466329)
  ·
    refine ⟨199296430672824289149349747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265728574230432385532466329 199296430672824289149349747)
    ·
      refine ⟨298944646009236433724024621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199296430672824289149349747 298944646009236433724024621)
      ·
        refine ⟨112104242253463662646509233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298944646009236433724024621 112104242253463662646509233)
        ·
          refine ⟨84078181690097746984881925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112104242253463662646509233 84078181690097746984881925)
          ·
            refine ⟨15764659066893327559665361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84078181690097746984881925 15764659066893327559665361)
            ·
              refine ⟨11823494300169995669749021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15764659066893327559665361 11823494300169995669749021)
              ·
                refine ⟨4433810362563748376155883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11823494300169995669749021 4433810362563748376155883)
                ·
                  refine ⟨6650715543845622564233825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4433810362563748376155883 6650715543845622564233825)
                  ·
                    refine ⟨4988036657884216923175369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6650715543845622564233825 4988036657884216923175369)
                    ·
                      refine ⟨3741027493413162692381527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988036657884216923175369 3741027493413162692381527)
                      ·
                        rfl

theorem cell23_7285625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_7285625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285625 prefixEnd_7285625 := by exact prefixLift 7285625
  have htrace : WordTrace (prefixWord ++ tailWord_7285625) baseStart_7285625 baseEnd_7285625 := by
    simpa [prefixWord, tailWord_7285625, baseEnd_7285625] using wordTrace_append hprefix tailTrace_7285625
  have hstable : (prefixWord ++ tailWord_7285625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285625).length < 2 ^ (prefixWord ++ tailWord_7285625).sum := by decide
  have hdescent : baseEnd_7285625 < baseStart_7285625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285641 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 3]
def baseStart_7285641 : Nat := 118140960795 + 7285641 * 2 ^ 59
def prefixEnd_7285641 : Nat := 4983230072969 + 3 ^ 40 * 7285641 * 2
def baseEnd_7285641 : Nat := 3741035709103634629781453

theorem tailTrace_7285641 : CollatzResearch.WordTrace tailWord_7285641 prefixEnd_7285641 3741035709103634629781453 := by
  unfold tailWord_7285641
  simp only [CollatzResearch.WordTrace]
  refine ⟨265729157798374420265048777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177152771865582946843365851 265729157798374420265048777)
  ·
    refine ⟨199296868348780815198786583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265729157798374420265048777 199296868348780815198786583)
    ·
      refine ⟨298945302523171222798179875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199296868348780815198786583 298945302523171222798179875)
      ·
        refine ⟨448417953784756834197269813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298945302523171222798179875 448417953784756834197269813)
        ·
          refine ⟨42039183167320953205994045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 448417953784756834197269813 42039183167320953205994045)
          ·
            refine ⟨15764693687745357452247767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42039183167320953205994045 15764693687745357452247767)
            ·
              refine ⟨23647040531618036178371651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15764693687745357452247767 23647040531618036178371651)
              ·
                refine ⟨35470560797427054267557477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23647040531618036178371651 35470560797427054267557477)
                ·
                  refine ⟨6650730149517572675167027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35470560797427054267557477 6650730149517572675167027)
                  ·
                    refine ⟨9976095224276359012750541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6650730149517572675167027 9976095224276359012750541)
                    ·
                      refine ⟨3741035709103634629781453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976095224276359012750541 3741035709103634629781453)
                      ·
                        rfl

theorem cell23_7285641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_7285641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285641 prefixEnd_7285641 := by exact prefixLift 7285641
  have htrace : WordTrace (prefixWord ++ tailWord_7285641) baseStart_7285641 baseEnd_7285641 := by
    simpa [prefixWord, tailWord_7285641, baseEnd_7285641] using wordTrace_append hprefix tailTrace_7285641
  have hstable : (prefixWord ++ tailWord_7285641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285641).length < 2 ^ (prefixWord ++ tailWord_7285641).sum := by decide
  have hdescent : baseEnd_7285641 < baseStart_7285641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285658 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_7285658 : Nat := 118140960795 + 7285658 * 2 ^ 59
def prefixEnd_7285658 : Nat := 4983230072969 + 3 ^ 40 * 7285658 * 2
def baseEnd_7285658 : Nat := 3741044438274761063268875

theorem tailTrace_7285658 : CollatzResearch.WordTrace tailWord_7285658 prefixEnd_7285658 3741044438274761063268875 := by
  unfold tailWord_7285658
  simp only [CollatzResearch.WordTrace]
  refine ⟨66432444459828208042104407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177153185226208554778945085 66432444459828208042104407)
  ·
    refine ⟨99648666689742312063156611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66432444459828208042104407 99648666689742312063156611)
    ·
      refine ⟨149473000034613468094734917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99648666689742312063156611 149473000034613468094734917)
      ·
        refine ⟨28026187506490025267762797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149473000034613468094734917 28026187506490025267762797)
        ·
          refine ⟨10509820314933759475411049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28026187506490025267762797 10509820314933759475411049)
          ·
            refine ⟨7882365236200319606558287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10509820314933759475411049 7882365236200319606558287)
            ·
              refine ⟨11823547854300479409837431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7882365236200319606558287 11823547854300479409837431)
              ·
                refine ⟨17735321781450719114756147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11823547854300479409837431 17735321781450719114756147)
                ·
                  refine ⟨26602982672176078672134221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17735321781450719114756147 26602982672176078672134221)
                  ·
                    refine ⟨9976118502066029502050333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26602982672176078672134221 9976118502066029502050333)
                    ·
                      refine ⟨3741044438274761063268875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976118502066029502050333 3741044438274761063268875)
                      ·
                        rfl

theorem cell23_7285658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_7285658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285658 prefixEnd_7285658 := by exact prefixLift 7285658
  have htrace : WordTrace (prefixWord ++ tailWord_7285658) baseStart_7285658 baseEnd_7285658 := by
    simpa [prefixWord, tailWord_7285658, baseEnd_7285658] using wordTrace_append hprefix tailTrace_7285658
  have hstable : (prefixWord ++ tailWord_7285658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285658).length < 2 ^ (prefixWord ++ tailWord_7285658).sum := by decide
  have hdescent : baseEnd_7285658 < baseStart_7285658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285668 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_7285668 : Nat := 118140960795 + 7285668 * 2 ^ 59
def prefixEnd_7285668 : Nat := 4983230072969 + 3 ^ 40 * 7285668 * 2
def baseEnd_7285668 : Nat := 3741049573081306024143829

theorem tailTrace_7285668 : CollatzResearch.WordTrace tailWord_7285668 prefixEnd_7285668 3741049573081306024143829 := by
  unfold tailWord_7285668
  simp only [CollatzResearch.WordTrace]
  refine ⟨132865071284638301938140829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177153428379517735917521105 132865071284638301938140829)
  ·
    refine ⟨49824401731739363226802811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132865071284638301938140829 49824401731739363226802811)
    ·
      refine ⟨74736602597609044840204217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49824401731739363226802811 74736602597609044840204217)
      ·
        refine ⟨56052451948206783630153163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74736602597609044840204217 56052451948206783630153163)
        ·
          refine ⟨84078677922310175445229745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56052451948206783630153163 84078677922310175445229745)
          ·
            refine ⟨63059008441732631583922309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84078677922310175445229745 63059008441732631583922309)
            ·
              refine ⟨11823564082824868421985433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63059008441732631583922309 11823564082824868421985433)
              ·
                refine ⟨8867673062118651316489075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11823564082824868421985433 8867673062118651316489075)
                ·
                  refine ⟨13301509593177976974733613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8867673062118651316489075 13301509593177976974733613)
                  ·
                    refine ⟨4988066097441741365525105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13301509593177976974733613 4988066097441741365525105)
                    ·
                      refine ⟨3741049573081306024143829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988066097441741365525105 3741049573081306024143829)
                      ·
                        rfl

theorem cell23_7285668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_7285668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285668 prefixEnd_7285668 := by exact prefixLift 7285668
  have htrace : WordTrace (prefixWord ++ tailWord_7285668) baseStart_7285668 baseEnd_7285668 := by
    simpa [prefixWord, tailWord_7285668, baseEnd_7285668] using wordTrace_append hprefix tailTrace_7285668
  have hstable : (prefixWord ++ tailWord_7285668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285668).length < 2 ^ (prefixWord ++ tailWord_7285668).sum := by decide
  have hdescent : baseEnd_7285668 < baseStart_7285668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285687 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 9]
def baseStart_7285687 : Nat := 118140960795 + 7285687 * 2 ^ 59
def prefixEnd_7285687 : Nat := 4983230072969 + 3 ^ 40 * 7285687 * 2
def baseEnd_7285687 : Nat := 415673258801526827756249

theorem tailTrace_7285687 : CollatzResearch.WordTrace tailWord_7285687 prefixEnd_7285687 415673258801526827756249 := by
  unfold tailWord_7285687
  simp only [CollatzResearch.WordTrace]
  refine ⟨265730835556207770121223315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177153890370805180080815543 265730835556207770121223315)
  ·
    refine ⟨398596253334311655181834973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265730835556207770121223315 398596253334311655181834973)
    ·
      refine ⟨149473595000366870693188115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398596253334311655181834973 149473595000366870693188115)
      ·
        refine ⟨224210392500550306039782173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149473595000366870693188115 224210392500550306039782173)
        ·
          refine ⟨84078897187706364764918315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224210392500550306039782173 84078897187706364764918315)
          ·
            refine ⟨126118345781559547147377473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84078897187706364764918315 126118345781559547147377473)
            ·
              refine ⟨94588759336169660360533105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126118345781559547147377473 94588759336169660360533105)
              ·
                refine ⟨70941569502127245270399829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94588759336169660360533105 70941569502127245270399829)
                ·
                  refine ⟨415673258801526827756249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70941569502127245270399829 415673258801526827756249)
                  ·
                    rfl

theorem cell23_7285687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 9].length) (baseStart_7285687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285687 prefixEnd_7285687 := by exact prefixLift 7285687
  have htrace : WordTrace (prefixWord ++ tailWord_7285687) baseStart_7285687 baseEnd_7285687 := by
    simpa [prefixWord, tailWord_7285687, baseEnd_7285687] using wordTrace_append hprefix tailTrace_7285687
  have hstable : (prefixWord ++ tailWord_7285687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285687).length < 2 ^ (prefixWord ++ tailWord_7285687).sum := by decide
  have hdescent : baseEnd_7285687 < baseStart_7285687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285709 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7285709 : Nat := 118140960795 + 7285709 * 2 ^ 59
def prefixEnd_7285709 : Nat := 4983230072969 + 3 ^ 40 * 7285709 * 2
def baseEnd_7285709 : Nat := 3741070625788140363731141

theorem tailTrace_7285709 : CollatzResearch.WordTrace tailWord_7285709 prefixEnd_7285709 3741070625788140363731141 := by
  unfold tailWord_7285709
  simp only [CollatzResearch.WordTrace]
  refine ⟨265731637962128067878524181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177154425308085378585682787 265731637962128067878524181)
  ·
    refine ⟨12456170529474753181805821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265731637962128067878524181 12456170529474753181805821)
    ·
      refine ⟨4671063948553032443177183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12456170529474753181805821 4671063948553032443177183)
      ·
        refine ⟨7006595922829548664765775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671063948553032443177183 7006595922829548664765775)
        ·
          refine ⟨10509893884244322997148663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006595922829548664765775 10509893884244322997148663)
          ·
            refine ⟨15764840826366484495722995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10509893884244322997148663 15764840826366484495722995)
            ·
              refine ⟨23647261239549726743584493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15764840826366484495722995 23647261239549726743584493)
              ·
                refine ⟨8867722964831147528844185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23647261239549726743584493 8867722964831147528844185)
                ·
                  refine ⟨6650792223623360646633139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8867722964831147528844185 6650792223623360646633139)
                  ·
                    refine ⟨9976188335435040969949709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6650792223623360646633139 9976188335435040969949709)
                    ·
                      refine ⟨3741070625788140363731141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976188335435040969949709 3741070625788140363731141)
                      ·
                        rfl

theorem cell23_7285709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7285709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285709 prefixEnd_7285709 := by exact prefixLift 7285709
  have htrace : WordTrace (prefixWord ++ tailWord_7285709) baseStart_7285709 baseEnd_7285709 := by
    simpa [prefixWord, tailWord_7285709, baseEnd_7285709] using wordTrace_append hprefix tailTrace_7285709
  have hstable : (prefixWord ++ tailWord_7285709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285709).length < 2 ^ (prefixWord ++ tailWord_7285709).sum := by decide
  have hdescent : baseEnd_7285709 < baseStart_7285709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285749 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7285749 : Nat := 118140960795 + 7285749 * 2 ^ 59
def prefixEnd_7285749 : Nat := 4983230072969 + 3 ^ 40 * 7285749 * 2
def baseEnd_7285749 : Nat := 3741091165014320207230957

theorem tailTrace_7285749 : CollatzResearch.WordTrace tailWord_7285749 prefixEnd_7285749 3741091165014320207230957 := by
  unfold tailWord_7285749
  simp only [CollatzResearch.WordTrace]
  refine ⟨265733096881983154709980301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177155397921322103139986867 265733096881983154709980301)
  ·
    refine ⟨99649911330743683016242613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265733096881983154709980301 99649911330743683016242613)
    ·
      refine ⟨9342179187257220282772745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99649911330743683016242613 9342179187257220282772745)
      ·
        refine ⟨7006634390442915212079559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9342179187257220282772745 7006634390442915212079559)
        ·
          refine ⟨10509951585664372818119339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006634390442915212079559 10509951585664372818119339)
          ·
            refine ⟨15764927378496559227179009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10509951585664372818119339 15764927378496559227179009)
            ·
              refine ⟨11823695533872419420384257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15764927378496559227179009 11823695533872419420384257)
              ·
                refine ⟨8867771650404314565288193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11823695533872419420384257 8867771650404314565288193)
                ·
                  refine ⟨6650828737803235923966145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8867771650404314565288193 6650828737803235923966145)
                  ·
                    refine ⟨4988121553352426942974609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6650828737803235923966145 4988121553352426942974609)
                    ·
                      refine ⟨3741091165014320207230957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988121553352426942974609 3741091165014320207230957)
                      ·
                        rfl

theorem cell23_7285749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7285749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285749 prefixEnd_7285749 := by exact prefixLift 7285749
  have htrace : WordTrace (prefixWord ++ tailWord_7285749) baseStart_7285749 baseEnd_7285749 := by
    simpa [prefixWord, tailWord_7285749, baseEnd_7285749] using wordTrace_append hprefix tailTrace_7285749
  have hstable : (prefixWord ++ tailWord_7285749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285749).length < 2 ^ (prefixWord ++ tailWord_7285749).sum := by decide
  have hdescent : baseEnd_7285749 < baseStart_7285749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285771 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 6, 2]
def baseStart_7285771 : Nat := 118140960795 + 7285771 * 2 ^ 59
def prefixEnd_7285771 : Nat := 4983230072969 + 3 ^ 40 * 7285771 * 2
def baseEnd_7285771 : Nat := 3741102461588719121155855

theorem tailTrace_7285771 : CollatzResearch.WordTrace tailWord_7285771 prefixEnd_7285771 3741102461588719121155855 := by
  unfold tailWord_7285771
  simp only [CollatzResearch.WordTrace]
  refine ⟨265733899287903452467281167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177155932858602301644854111 265733899287903452467281167)
  ·
    refine ⟨398600848931855178700921751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265733899287903452467281167 398600848931855178700921751)
    ·
      refine ⟨597901273397782768051382627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398600848931855178700921751 597901273397782768051382627)
      ·
        refine ⟨896851910096674152077073941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597901273397782768051382627 896851910096674152077073941)
        ·
          refine ⟨42039933285781600878612841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 896851910096674152077073941 42039933285781600878612841)
          ·
            refine ⟨31529949964336200658959631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42039933285781600878612841 31529949964336200658959631)
            ·
              refine ⟨47294924946504300988439447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31529949964336200658959631 47294924946504300988439447)
              ·
                refine ⟨70942387419756451482659171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47294924946504300988439447 70942387419756451482659171)
                ·
                  refine ⟨106413581129634677223988757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70942387419756451482659171 106413581129634677223988757)
                  ·
                    refine ⟨4988136615451625494874473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106413581129634677223988757 4988136615451625494874473)
                    ·
                      refine ⟨3741102461588719121155855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988136615451625494874473 3741102461588719121155855)
                      ·
                        rfl

theorem cell23_7285771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6, 2].length) (baseStart_7285771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285771 prefixEnd_7285771 := by exact prefixLift 7285771
  have htrace : WordTrace (prefixWord ++ tailWord_7285771) baseStart_7285771 baseEnd_7285771 := by
    simpa [prefixWord, tailWord_7285771, baseEnd_7285771] using wordTrace_append hprefix tailTrace_7285771
  have hstable : (prefixWord ++ tailWord_7285771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285771).length < 2 ^ (prefixWord ++ tailWord_7285771).sum := by decide
  have hdescent : baseEnd_7285771 < baseStart_7285771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285781 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_7285781 : Nat := 118140960795 + 7285781 * 2 ^ 59
def prefixEnd_7285781 : Nat := 4983230072969 + 3 ^ 40 * 7285781 * 2
def baseEnd_7285781 : Nat := 1247035865465088027343603

theorem tailTrace_7285781 : CollatzResearch.WordTrace tailWord_7285781 prefixEnd_7285781 1247035865465088027343603 := by
  unfold tailWord_7285781
  simp only [CollatzResearch.WordTrace]
  refine ⟨265734264017867224175145197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177156176011911482783430131 265734264017867224175145197)
  ·
    refine ⟨99650349006700209065679449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265734264017867224175145197 99650349006700209065679449)
    ·
      refine ⟨74737761755025156799259587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99650349006700209065679449 74737761755025156799259587)
      ·
        refine ⟨112106642632537735198889381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74737761755025156799259587 112106642632537735198889381)
        ·
          refine ⟨21019995493600825349791759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112106642632537735198889381 21019995493600825349791759)
          ·
            refine ⟨31529993240401238024687639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21019995493600825349791759 31529993240401238024687639)
            ·
              refine ⟨47294989860601857037031459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31529993240401238024687639 47294989860601857037031459)
              ·
                refine ⟨70942484790902785555547189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47294989860601857037031459 70942484790902785555547189)
                ·
                  refine ⟨6650857949147136145832549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70942484790902785555547189 6650857949147136145832549)
                  ·
                    refine ⟨1247035865465088027343603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6650857949147136145832549 1247035865465088027343603)
                    ·
                      rfl

theorem cell23_7285781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_7285781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285781 prefixEnd_7285781 := by exact prefixLift 7285781
  have htrace : WordTrace (prefixWord ++ tailWord_7285781) baseStart_7285781 baseEnd_7285781 := by
    simpa [prefixWord, tailWord_7285781, baseEnd_7285781] using wordTrace_append hprefix tailTrace_7285781
  have hstable : (prefixWord ++ tailWord_7285781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285781).length < 2 ^ (prefixWord ++ tailWord_7285781).sum := by decide
  have hdescent : baseEnd_7285781 < baseStart_7285781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285791 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_7285791 : Nat := 118140960795 + 7285791 * 2 ^ 59
def prefixEnd_7285791 : Nat := 4983230072969 + 3 ^ 40 * 7285791 * 2
def baseEnd_7285791 : Nat := 3741112731201809042905763

theorem tailTrace_7285791 : CollatzResearch.WordTrace tailWord_7285791 prefixEnd_7285791 3741112731201809042905763 := by
  unfold tailWord_7285791
  simp only [CollatzResearch.WordTrace]
  refine ⟨265734628747830995883009227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177156419165220663922006151 265734628747830995883009227)
  ·
    refine ⟨398601943121746493824513841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265734628747830995883009227 398601943121746493824513841)
    ·
      refine ⟨298951457341309870368385381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398601943121746493824513841 298951457341309870368385381)
      ·
        refine ⟨56053398251495600694072259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298951457341309870368385381 56053398251495600694072259)
        ·
          refine ⟨84080097377243401041108389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56053398251495600694072259 84080097377243401041108389)
          ·
            refine ⟨15765018258233137695207823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84080097377243401041108389 15765018258233137695207823)
            ·
              refine ⟨23647527387349706542811735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15765018258233137695207823 23647527387349706542811735)
              ·
                refine ⟨35471291081024559814217603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23647527387349706542811735 35471291081024559814217603)
                ·
                  refine ⟨53206936621536839721326405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35471291081024559814217603 53206936621536839721326405)
                  ·
                    refine ⟨9976300616538157447748701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53206936621536839721326405 9976300616538157447748701)
                    ·
                      refine ⟨3741112731201809042905763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976300616538157447748701 3741112731201809042905763)
                      ·
                        rfl

theorem cell23_7285791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_7285791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285791 prefixEnd_7285791 := by exact prefixLift 7285791
  have htrace : WordTrace (prefixWord ++ tailWord_7285791) baseStart_7285791 baseEnd_7285791 := by
    simpa [prefixWord, tailWord_7285791, baseEnd_7285791] using wordTrace_append hprefix tailTrace_7285791
  have hstable : (prefixWord ++ tailWord_7285791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285791).length < 2 ^ (prefixWord ++ tailWord_7285791).sum := by decide
  have hdescent : baseEnd_7285791 < baseStart_7285791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285834 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_7285834 : Nat := 118140960795 + 7285834 * 2 ^ 59
def prefixEnd_7285834 : Nat := 4983230072969 + 3 ^ 40 * 7285834 * 2
def baseEnd_7285834 : Nat := 3741134810869952374668065

theorem tailTrace_7285834 : CollatzResearch.WordTrace tailWord_7285834 prefixEnd_7285834 3741134810869952374668065 := by
  unfold tailWord_7285834
  simp only [CollatzResearch.WordTrace]
  refine ⟨66434049271668803556706139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177157464724450142817883037 66434049271668803556706139)
  ·
    refine ⟨99651073907503205335059209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66434049271668803556706139 99651073907503205335059209)
    ·
      refine ⟨74738305430627404001294407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99651073907503205335059209 74738305430627404001294407)
      ·
        refine ⟨112107458145941106001941611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74738305430627404001294407 112107458145941106001941611)
        ·
          refine ⟨168161187218911659002912417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112107458145941106001941611 168161187218911659002912417)
          ·
            refine ⟨126120890414183744252184313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168161187218911659002912417 126120890414183744252184313)
            ·
              refine ⟨94590667810637808189138235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126120890414183744252184313 94590667810637808189138235)
              ·
                refine ⟨141886001715956712283707353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94590667810637808189138235 141886001715956712283707353)
                ·
                  refine ⟨106414501286967534212780515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141886001715956712283707353 106414501286967534212780515)
                  ·
                    refine ⟨159621751930451301319170773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106414501286967534212780515 159621751930451301319170773)
                    ·
                      refine ⟨3741134810869952374668065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159621751930451301319170773 3741134810869952374668065)
                      ·
                        rfl

theorem cell23_7285834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_7285834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285834 prefixEnd_7285834 := by exact prefixLift 7285834
  have htrace : WordTrace (prefixWord ++ tailWord_7285834) baseStart_7285834 baseEnd_7285834 := by
    simpa [prefixWord, tailWord_7285834, baseEnd_7285834] using wordTrace_append hprefix tailTrace_7285834
  have hstable : (prefixWord ++ tailWord_7285834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285834).length < 2 ^ (prefixWord ++ tailWord_7285834).sum := by decide
  have hdescent : baseEnd_7285834 < baseStart_7285834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285838 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_7285838 : Nat := 118140960795 + 7285838 * 2 ^ 59
def prefixEnd_7285838 : Nat := 4983230072969 + 3 ^ 40 * 7285838 * 2
def baseEnd_7285838 : Nat := 3741136864792570359018047

theorem tailTrace_7285838 : CollatzResearch.WordTrace tailWord_7285838 prefixEnd_7285838 3741136864792570359018047 := by
  unfold tailWord_7285838
  simp only [CollatzResearch.WordTrace]
  refine ⟨33217042872332590363746271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177157561985773815273313445 33217042872332590363746271)
  ·
    refine ⟨49825564308498885545619407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33217042872332590363746271 49825564308498885545619407)
    ·
      refine ⟨74738346462748328318429111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49825564308498885545619407 74738346462748328318429111)
      ·
        refine ⟨112107519694122492477643667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74738346462748328318429111 112107519694122492477643667)
        ·
          refine ⟨168161279541183738716465501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112107519694122492477643667 168161279541183738716465501)
          ·
            refine ⟨63060479827943902018674563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168161279541183738716465501 63060479827943902018674563)
            ·
              refine ⟨94590719741915853028011845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63060479827943902018674563 94590719741915853028011845)
              ·
                refine ⟨17735759951609222442752221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94590719741915853028011845 17735759951609222442752221)
                ·
                  refine ⟨6650909981853458416032083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17735759951609222442752221 6650909981853458416032083)
                  ·
                    refine ⟨9976364972780187624048125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6650909981853458416032083 9976364972780187624048125)
                    ·
                      refine ⟨3741136864792570359018047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976364972780187624048125 3741136864792570359018047)
                      ·
                        rfl

theorem cell23_7285838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_7285838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285838 prefixEnd_7285838 := by exact prefixLift 7285838
  have htrace : WordTrace (prefixWord ++ tailWord_7285838) baseStart_7285838 baseEnd_7285838 := by
    simpa [prefixWord, tailWord_7285838, baseEnd_7285838] using wordTrace_append hprefix tailTrace_7285838
  have hstable : (prefixWord ++ tailWord_7285838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285838).length < 2 ^ (prefixWord ++ tailWord_7285838).sum := by decide
  have hdescent : baseEnd_7285838 < baseStart_7285838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285841 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 1, 5]
def baseStart_7285841 : Nat := 118140960795 + 7285841 * 2 ^ 59
def prefixEnd_7285841 : Nat := 4983230072969 + 3 ^ 40 * 7285841 * 2
def baseEnd_7285841 : Nat := 1247046135078177949093511

theorem tailTrace_7285841 : CollatzResearch.WordTrace tailWord_7285841 prefixEnd_7285841 1247046135078177949093511 := by
  unfold tailWord_7285841
  simp only [CollatzResearch.WordTrace]
  refine ⟨265736452397649854422329377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177157634931766569614886251 265736452397649854422329377)
  ·
    refine ⟨199302339298237390816747033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265736452397649854422329377 199302339298237390816747033)
    ·
      refine ⟨149476754473678043112560275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199302339298237390816747033 149476754473678043112560275)
      ·
        refine ⟨224215131710517064668840413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149476754473678043112560275 224215131710517064668840413)
        ·
          refine ⟨84080674391443899250815155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224215131710517064668840413 84080674391443899250815155)
          ·
            refine ⟨126121011587165848876222733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84080674391443899250815155 126121011587165848876222733)
            ·
              refine ⟨47295379345187193328583525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126121011587165848876222733 47295379345187193328583525)
              ·
                refine ⟨8867883627222598749109411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47295379345187193328583525 8867883627222598749109411)
                ·
                  refine ⟨13301825440833898123664117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8867883627222598749109411 13301825440833898123664117)
                  ·
                    refine ⟨1247046135078177949093511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13301825440833898123664117 1247046135078177949093511)
                    ·
                      rfl

theorem cell23_7285841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_7285841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285841 prefixEnd_7285841 := by exact prefixLift 7285841
  have htrace : WordTrace (prefixWord ++ tailWord_7285841) baseStart_7285841 baseEnd_7285841 := by
    simpa [prefixWord, tailWord_7285841, baseEnd_7285841] using wordTrace_append hprefix tailTrace_7285841
  have hstable : (prefixWord ++ tailWord_7285841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285841).length < 2 ^ (prefixWord ++ tailWord_7285841).sum := by decide
  have hdescent : baseEnd_7285841 < baseStart_7285841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285848 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 2, 3, 2]
def baseStart_7285848 : Nat := 118140960795 + 7285848 * 2 ^ 59
def prefixEnd_7285848 : Nat := 4983230072969 + 3 ^ 40 * 7285848 * 2
def baseEnd_7285848 : Nat := 3741141999599115319893001

theorem tailTrace_7285848 : CollatzResearch.WordTrace tailWord_7285848 prefixEnd_7285848 3741141999599115319893001 := by
  unfold tailWord_7285848
  simp only [CollatzResearch.WordTrace]
  refine ⟨132868353854312247308917099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177157805139082996411889465 132868353854312247308917099)
  ·
    refine ⟨199302530781468370963375649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132868353854312247308917099 199302530781468370963375649)
    ·
      refine ⟨149476898086101278222531737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199302530781468370963375649 149476898086101278222531737)
      ·
        refine ⟨112107673564575958666898803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149476898086101278222531737 112107673564575958666898803)
        ·
          refine ⟨168161510346863938000348205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112107673564575958666898803 168161510346863938000348205)
          ·
            refine ⟨63060566380073976750130577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168161510346863938000348205 63060566380073976750130577)
            ·
              refine ⟨47295424785055482562597933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63060566380073976750130577 47295424785055482562597933)
              ·
                refine ⟨17735784294395805960974225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47295424785055482562597933 17735784294395805960974225)
                ·
                  refine ⟨13301838220796854470730669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17735784294395805960974225 13301838220796854470730669)
                  ·
                    refine ⟨4988189332798820426524001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13301838220796854470730669 4988189332798820426524001)
                    ·
                      refine ⟨3741141999599115319893001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988189332798820426524001 3741141999599115319893001)
                      ·
                        rfl

theorem cell23_7285848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_7285848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285848 prefixEnd_7285848 := by exact prefixLift 7285848
  have htrace : WordTrace (prefixWord ++ tailWord_7285848) baseStart_7285848 baseEnd_7285848 := by
    simpa [prefixWord, tailWord_7285848, baseEnd_7285848] using wordTrace_append hprefix tailTrace_7285848
  have hstable : (prefixWord ++ tailWord_7285848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285848).length < 2 ^ (prefixWord ++ tailWord_7285848).sum := by decide
  have hdescent : baseEnd_7285848 < baseStart_7285848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285871 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 4, 4]
def baseStart_7285871 : Nat := 118140960795 + 7285871 * 2 ^ 59
def prefixEnd_7285871 : Nat := 4983230072969 + 3 ^ 40 * 7285871 * 2
def baseEnd_7285871 : Nat := 1247051269884722909968465

theorem tailTrace_7285871 : CollatzResearch.WordTrace tailWord_7285871 prefixEnd_7285871 1247051269884722909968465 := by
  unfold tailWord_7285871
  simp only [CollatzResearch.WordTrace]
  refine ⟨265737546587541169545921467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177158364391694113030614311 265737546587541169545921467)
  ·
    refine ⟨398606319881311754318882201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265737546587541169545921467 398606319881311754318882201)
    ·
      refine ⟨298954739910983815739161651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398606319881311754318882201 298954739910983815739161651)
      ·
        refine ⟨448432109866475723608742477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298954739910983815739161651 448432109866475723608742477)
        ·
          refine ⟨168162041199928396353278429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448432109866475723608742477 168162041199928396353278429)
          ·
            refine ⟨63060765449973148632479411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168162041199928396353278429 63060765449973148632479411)
            ·
              refine ⟨94591148174959722948719117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63060765449973148632479411 94591148174959722948719117)
              ·
                refine ⟨35471680565609896105769669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94591148174959722948719117 35471680565609896105769669)
                ·
                  refine ⟨6650940106051855519831813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35471680565609896105769669 6650940106051855519831813)
                  ·
                    refine ⟨1247051269884722909968465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6650940106051855519831813 1247051269884722909968465)
                    ·
                      rfl

theorem cell23_7285871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_7285871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285871 prefixEnd_7285871 := by exact prefixLift 7285871
  have htrace : WordTrace (prefixWord ++ tailWord_7285871) baseStart_7285871 baseEnd_7285871 := by
    simpa [prefixWord, tailWord_7285871, baseEnd_7285871] using wordTrace_append hprefix tailTrace_7285871
  have hstable : (prefixWord ++ tailWord_7285871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285871).length < 2 ^ (prefixWord ++ tailWord_7285871).sum := by decide
  have hdescent : baseEnd_7285871 < baseStart_7285871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285872 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 1, 1, 3]
def baseStart_7285872 : Nat := 118140960795 + 7285872 * 2 ^ 59
def prefixEnd_7285872 : Nat := 4983230072969 + 3 ^ 40 * 7285872 * 2
def baseEnd_7285872 : Nat := 3741154323134823225992891

theorem tailTrace_7285872 : CollatzResearch.WordTrace tailWord_7285872 prefixEnd_7285872 3741154323134823225992891 := by
  unfold tailWord_7285872
  simp only [CollatzResearch.WordTrace]
  refine ⟨132868791530268773358353935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177158388707025031144471913 132868791530268773358353935)
  ·
    refine ⟨199303187295403160037530903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132868791530268773358353935 199303187295403160037530903)
    ·
      refine ⟨298954780943104740056296355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199303187295403160037530903 298954780943104740056296355)
      ·
        refine ⟨448432171414657110084444533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298954780943104740056296355 448432171414657110084444533)
        ·
          refine ⟨42040516070124104070416675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 448432171414657110084444533 42040516070124104070416675)
          ·
            refine ⟨63060774105186156105625013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42040516070124104070416675 63060774105186156105625013)
            ·
              refine ⟨5911947572361202134902345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63060774105186156105625013 5911947572361202134902345)
              ·
                refine ⟨4433960679270901601176759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911947572361202134902345 4433960679270901601176759)
                ·
                  refine ⟨6650941018906352401765139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4433960679270901601176759 6650941018906352401765139)
                  ·
                    refine ⟨9976411528359528602647709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6650941018906352401765139 9976411528359528602647709)
                    ·
                      refine ⟨3741154323134823225992891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976411528359528602647709 3741154323134823225992891)
                      ·
                        rfl

theorem cell23_7285872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 1, 1, 3].length) (baseStart_7285872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285872 prefixEnd_7285872 := by exact prefixLift 7285872
  have htrace : WordTrace (prefixWord ++ tailWord_7285872) baseStart_7285872 baseEnd_7285872 := by
    simpa [prefixWord, tailWord_7285872, baseEnd_7285872] using wordTrace_append hprefix tailTrace_7285872
  have hstable : (prefixWord ++ tailWord_7285872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285872).length < 2 ^ (prefixWord ++ tailWord_7285872).sum := by decide
  have hdescent : baseEnd_7285872 < baseStart_7285872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285878 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7285878 : Nat := 118140960795 + 7285878 * 2 ^ 59
def prefixEnd_7285878 : Nat := 4983230072969 + 3 ^ 40 * 7285878 * 2
def baseEnd_7285878 : Nat := 3741157404018750202517863

theorem tailTrace_7285878 : CollatzResearch.WordTrace tailWord_7285878 prefixEnd_7285878 3741157404018750202517863 := by
  unfold tailWord_7285878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16608612618657238108839143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177158534599010539827617525 16608612618657238108839143)
  ·
    refine ⟨24912918927985857163258715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16608612618657238108839143 24912918927985857163258715)
    ·
      refine ⟨37369378391978785744888073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24912918927985857163258715 37369378391978785744888073)
      ·
        refine ⟨28027033793984089308666055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37369378391978785744888073 28027033793984089308666055)
        ·
          refine ⟨42040550690976133962999083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28027033793984089308666055 42040550690976133962999083)
          ·
            refine ⟨63060826036464200944498625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42040550690976133962999083 63060826036464200944498625)
            ·
              refine ⟨47295619527348150708373969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63060826036464200944498625 47295619527348150708373969)
              ·
                refine ⟨35471714645511113031280477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47295619527348150708373969 35471714645511113031280477)
                ·
                  refine ⟨13301892992066667386730179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35471714645511113031280477 13301892992066667386730179)
                  ·
                    refine ⟨19952839488100001080095269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13301892992066667386730179 19952839488100001080095269)
                    ·
                      refine ⟨3741157404018750202517863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19952839488100001080095269 3741157404018750202517863)
                      ·
                        rfl

theorem cell23_7285878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7285878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285878 prefixEnd_7285878 := by exact prefixLift 7285878
  have htrace : WordTrace (prefixWord ++ tailWord_7285878) baseStart_7285878 baseEnd_7285878 := by
    simpa [prefixWord, tailWord_7285878, baseEnd_7285878] using wordTrace_append hprefix tailTrace_7285878
  have hstable : (prefixWord ++ tailWord_7285878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285878).length < 2 ^ (prefixWord ++ tailWord_7285878).sum := by decide
  have hdescent : baseEnd_7285878 < baseStart_7285878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285891 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4]
def baseStart_7285891 : Nat := 118140960795 + 7285891 * 2 ^ 59
def prefixEnd_7285891 : Nat := 4983230072969 + 3 ^ 40 * 7285891 * 2
def baseEnd_7285891 : Nat := 3741164079267258651655303

theorem tailTrace_7285891 : CollatzResearch.WordTrace tailWord_7285891 prefixEnd_7285891 3741164079267258651655303 := by
  unfold tailWord_7285891
  simp only [CollatzResearch.WordTrace]
  refine ⟨265738276047468712961649527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177158850698312475307766351 265738276047468712961649527)
  ·
    refine ⟨398607414071203069442474291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265738276047468712961649527 398607414071203069442474291)
    ·
      refine ⟨597911121106804604163711437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398607414071203069442474291 597911121106804604163711437)
      ·
        refine ⟨224216670415051726561391789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597911121106804604163711437 224216670415051726561391789)
        ·
          refine ⟨84081251405644397460521921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224216670415051726561391789 84081251405644397460521921)
          ·
            refine ⟨63060938554233298095391441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84081251405644397460521921 63060938554233298095391441)
            ·
              refine ⟨47295703915674973571543581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63060938554233298095391441 47295703915674973571543581)
              ·
                refine ⟨17735888968378115089328843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47295703915674973571543581 17735888968378115089328843)
                ·
                  refine ⟨26603833452567172633993265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17735888968378115089328843 26603833452567172633993265)
                  ·
                    refine ⟨19952875089425379475494949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26603833452567172633993265 19952875089425379475494949)
                    ·
                      refine ⟨3741164079267258651655303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19952875089425379475494949 3741164079267258651655303)
                      ·
                        rfl

theorem cell23_7285891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_7285891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285891 prefixEnd_7285891 := by exact prefixLift 7285891
  have htrace : WordTrace (prefixWord ++ tailWord_7285891) baseStart_7285891 baseEnd_7285891 := by
    simpa [prefixWord, tailWord_7285891, baseEnd_7285891] using wordTrace_append hprefix tailTrace_7285891
  have hstable : (prefixWord ++ tailWord_7285891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285891).length < 2 ^ (prefixWord ++ tailWord_7285891).sum := by decide
  have hdescent : baseEnd_7285891 < baseStart_7285891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285898 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_7285898 : Nat := 118140960795 + 7285898 * 2 ^ 59
def prefixEnd_7285898 : Nat := 4983230072969 + 3 ^ 40 * 7285898 * 2
def baseEnd_7285898 : Nat := 3741167673631840124267771

theorem tailTrace_7285898 : CollatzResearch.WordTrace tailWord_7285898 prefixEnd_7285898 3741167673631840124267771 := by
  unfold tailWord_7285898
  simp only [CollatzResearch.WordTrace]
  refine ⟨66434632839610838289288587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177159020905628902104769565 66434632839610838289288587)
  ·
    refine ⟨99651949259416257433932881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66434632839610838289288587 99651949259416257433932881)
    ·
      refine ⟨74738961944562193075449661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99651949259416257433932881 74738961944562193075449661)
      ·
        refine ⟨28027110729210822403293623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74738961944562193075449661 28027110729210822403293623)
        ·
          refine ⟨42040666093816233604940435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28027110729210822403293623 42040666093816233604940435)
          ·
            refine ⟨63060999140724350407410653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42040666093816233604940435 63060999140724350407410653)
            ·
              refine ⟨23647874677771631402778995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63060999140724350407410653 23647874677771631402778995)
              ·
                refine ⟨35471812016657447104168493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23647874677771631402778995 35471812016657447104168493)
                ·
                  refine ⟨13301929506246542664063185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35471812016657447104168493 13301929506246542664063185)
                  ·
                    refine ⟨9976447129684906998047389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13301929506246542664063185 9976447129684906998047389)
                    ·
                      refine ⟨3741167673631840124267771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976447129684906998047389 3741167673631840124267771)
                      ·
                        rfl

theorem cell23_7285898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_7285898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285898 prefixEnd_7285898 := by exact prefixLift 7285898
  have htrace : WordTrace (prefixWord ++ tailWord_7285898) baseStart_7285898 baseEnd_7285898 := by
    simpa [prefixWord, tailWord_7285898, baseEnd_7285898] using wordTrace_append hprefix tailTrace_7285898
  have hstable : (prefixWord ++ tailWord_7285898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285898).length < 2 ^ (prefixWord ++ tailWord_7285898).sum := by decide
  have hdescent : baseEnd_7285898 < baseStart_7285898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285922 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7285922 : Nat := 118140960795 + 7285922 * 2 ^ 59
def prefixEnd_7285922 : Nat := 4983230072969 + 3 ^ 40 * 7285922 * 2
def baseEnd_7285922 : Nat := 1247059999055849343455887

theorem tailTrace_7285922 : CollatzResearch.WordTrace tailWord_7285922 prefixEnd_7285922 1247059999055849343455887 := by
  unfold tailWord_7285922
  simp only [CollatzResearch.WordTrace]
  refine ⟨66434851677589101314007005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177159604473570936837352013 66434851677589101314007005)
  ·
    refine ⟨24913069379095912992752627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66434851677589101314007005 24913069379095912992752627)
    ·
      refine ⟨37369604068643869489128941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24913069379095912992752627 37369604068643869489128941)
      ·
        refine ⟨14013601525741451058423353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37369604068643869489128941 14013601525741451058423353)
        ·
          refine ⟨10510201144306088293817515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14013601525741451058423353 10510201144306088293817515)
          ·
            refine ⟨15765301716459132440726273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10510201144306088293817515 15765301716459132440726273)
            ·
              refine ⟨11823976287344349330544705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15765301716459132440726273 11823976287344349330544705)
              ·
                refine ⟨8867982215508261997908529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11823976287344349330544705 8867982215508261997908529)
                ·
                  refine ⟨6650986661631196498431397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8867982215508261997908529 6650986661631196498431397)
                  ·
                    refine ⟨1247059999055849343455887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6650986661631196498431397 1247059999055849343455887)
                    ·
                      rfl

theorem cell23_7285922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7285922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285922 prefixEnd_7285922 := by exact prefixLift 7285922
  have htrace : WordTrace (prefixWord ++ tailWord_7285922) baseStart_7285922 baseEnd_7285922 := by
    simpa [prefixWord, tailWord_7285922, baseEnd_7285922] using wordTrace_append hprefix tailTrace_7285922
  have hstable : (prefixWord ++ tailWord_7285922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285922).length < 2 ^ (prefixWord ++ tailWord_7285922).sum := by decide
  have hdescent : baseEnd_7285922 < baseStart_7285922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285945 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7285945 : Nat := 118140960795 + 7285945 * 2 ^ 59
def prefixEnd_7285945 : Nat := 4983230072969 + 3 ^ 40 * 7285945 * 2
def baseEnd_7285945 : Nat := 3741191807222601440380055

theorem tailTrace_7285945 : CollatzResearch.WordTrace tailWord_7285945 prefixEnd_7285945 3741191807222601440380055 := by
  unfold tailWord_7285945
  simp only [CollatzResearch.WordTrace]
  refine ⟨265740245589273080184115289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177160163726182053456076859 265740245589273080184115289)
  ·
    refine ⟨199305184191954810138086467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265740245589273080184115289 199305184191954810138086467)
    ·
      refine ⟨298957776287932215207129701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199305184191954810138086467 298957776287932215207129701)
      ·
        refine ⟨56054583053987290351336819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298957776287932215207129701 56054583053987290351336819)
        ·
          refine ⟨84081874580980935527005229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56054583053987290351336819 84081874580980935527005229)
          ·
            refine ⟨31530702967867850822626961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84081874580980935527005229 31530702967867850822626961)
            ·
              refine ⟨23648027225900888116970221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31530702967867850822626961 23648027225900888116970221)
              ·
                refine ⟨8868010209712833043863833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23648027225900888116970221 8868010209712833043863833)
                ·
                  refine ⟨6651007657284624782897875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8868010209712833043863833 6651007657284624782897875)
                  ·
                    refine ⟨9976511485926937174346813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6651007657284624782897875 9976511485926937174346813)
                    ·
                      refine ⟨3741191807222601440380055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976511485926937174346813 3741191807222601440380055)
                      ·
                        rfl

theorem cell23_7285945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7285945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285945 prefixEnd_7285945 := by exact prefixLift 7285945
  have htrace : WordTrace (prefixWord ++ tailWord_7285945) baseStart_7285945 baseEnd_7285945 := by
    simpa [prefixWord, tailWord_7285945, baseEnd_7285945] using wordTrace_append hprefix tailTrace_7285945
  have hstable : (prefixWord ++ tailWord_7285945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285945).length < 2 ^ (prefixWord ++ tailWord_7285945).sum := by decide
  have hdescent : baseEnd_7285945 < baseStart_7285945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285971 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 3]
def baseStart_7285971 : Nat := 118140960795 + 7285971 * 2 ^ 59
def prefixEnd_7285971 : Nat := 4983230072969 + 3 ^ 40 * 7285971 * 2
def baseEnd_7285971 : Nat := 3741205157719618338654935

theorem tailTrace_7285971 : CollatzResearch.WordTrace tailWord_7285971 prefixEnd_7285971 3741205157719618338654935 := by
  unfold tailWord_7285971
  simp only [CollatzResearch.WordTrace]
  refine ⟨265741193887178886624561767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177160795924785924416374511 265741193887178886624561767)
  ·
    refine ⟨398611790830768329936842651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265741193887178886624561767 398611790830768329936842651)
    ·
      refine ⟨597917686246152494905263977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398611790830768329936842651 597917686246152494905263977)
      ·
        refine ⟨448438264684614371178947983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597917686246152494905263977 448438264684614371178947983)
        ·
          refine ⟨672657397026921556768421975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448438264684614371178947983 672657397026921556768421975)
          ·
            refine ⟨1008986095540382335152632963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672657397026921556768421975 1008986095540382335152632963)
            ·
              refine ⟨1513479143310573502728949445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008986095540382335152632963 1513479143310573502728949445)
              ·
                refine ⟨283777339370732531761678021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1513479143310573502728949445 283777339370732531761678021)
                ·
                  refine ⟨53208251132012349705314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283777339370732531761678021 53208251132012349705314629)
                  ·
                    refine ⟨9976547087252315569746493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53208251132012349705314629 9976547087252315569746493)
                    ·
                      refine ⟨3741205157719618338654935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9976547087252315569746493 3741205157719618338654935)
                      ·
                        rfl

theorem cell23_7285971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_7285971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285971 prefixEnd_7285971 := by exact prefixLift 7285971
  have htrace : WordTrace (prefixWord ++ tailWord_7285971) baseStart_7285971 baseEnd_7285971 := by
    simpa [prefixWord, tailWord_7285971, baseEnd_7285971] using wordTrace_append hprefix tailTrace_7285971
  have hstable : (prefixWord ++ tailWord_7285971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285971).length < 2 ^ (prefixWord ++ tailWord_7285971).sum := by decide
  have hdescent : baseEnd_7285971 < baseStart_7285971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7285998 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7285998 : Nat := 118140960795 + 7285998 * 2 ^ 59
def prefixEnd_7285998 : Nat := 4983230072969 + 3 ^ 40 * 7285998 * 2
def baseEnd_7285998 : Nat := 3741219021697289733017311

theorem tailTrace_7285998 : CollatzResearch.WordTrace tailWord_7285998 prefixEnd_7285998 3741219021697289733017311 := by
  unfold tailWord_7285998
  simp only [CollatzResearch.WordTrace]
  refine ⟨33217772332260133779474331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177161452438720713490529765 33217772332260133779474331)
  ·
    refine ⟨49826658498390200669211497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33217772332260133779474331 49826658498390200669211497)
    ·
      refine ⟨37369993873792650501908623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49826658498390200669211497 37369993873792650501908623)
      ·
        refine ⟨56054990810688975752862935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37369993873792650501908623 56054990810688975752862935)
        ·
          refine ⟨84082486216033463629294403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56054990810688975752862935 84082486216033463629294403)
          ·
            refine ⟨126123729324050195443941605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84082486216033463629294403 126123729324050195443941605)
            ·
              refine ⟨23648199248259411645739051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126123729324050195443941605 23648199248259411645739051)
              ·
                refine ⟨35472298872389117468608577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23648199248259411645739051 35472298872389117468608577)
                ·
                  refine ⟨26604224154291838101456433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35472298872389117468608577 26604224154291838101456433)
                  ·
                    refine ⟨19953168115718878576092325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26604224154291838101456433 19953168115718878576092325)
                    ·
                      refine ⟨3741219021697289733017311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19953168115718878576092325 3741219021697289733017311)
                      ·
                        rfl

theorem cell23_7285998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7285998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7285998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7285998 prefixEnd_7285998 := by exact prefixLift 7285998
  have htrace : WordTrace (prefixWord ++ tailWord_7285998) baseStart_7285998 baseEnd_7285998 := by
    simpa [prefixWord, tailWord_7285998, baseEnd_7285998] using wordTrace_append hprefix tailTrace_7285998
  have hstable : (prefixWord ++ tailWord_7285998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7285998).length < 2 ^ (prefixWord ++ tailWord_7285998).sum := by decide
  have hdescent : baseEnd_7285998 < baseStart_7285998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7285998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286021 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_7286021 : Nat := 118140960795 + 7286021 * 2 ^ 59
def prefixEnd_7286021 : Nat := 4983230072969 + 3 ^ 40 * 7286021 * 2
def baseEnd_7286021 : Nat := 1247076943917447714343235

theorem tailTrace_7286021 : CollatzResearch.WordTrace tailWord_7286021 prefixEnd_7286021 1247076943917447714343235 := by
  unfold tailWord_7286021
  simp only [CollatzResearch.WordTrace]
  refine ⟨265743017536997745163881917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177162011691331830109254611 265743017536997745163881917)
  ·
    refine ⟨99653631576374154436455719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265743017536997745163881917 99653631576374154436455719)
    ·
      refine ⟨149480447364561231654683579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99653631576374154436455719 149480447364561231654683579)
      ·
        refine ⟨224220671046841847482025369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149480447364561231654683579 224220671046841847482025369)
        ·
          refine ⟨168165503285131385611519027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224220671046841847482025369 168165503285131385611519027)
          ·
            refine ⟨252248254927697078417278541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168165503285131385611519027 252248254927697078417278541)
            ·
              refine ⟨94593095597886404406479453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252248254927697078417278541 94593095597886404406479453)
              ·
                refine ⟨35472410849207401652429795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94593095597886404406479453 35472410849207401652429795)
                ·
                  refine ⟨53208616273811102478644693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35472410849207401652429795 53208616273811102478644693)
                  ·
                    refine ⟨1247076943917447714343235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53208616273811102478644693 1247076943917447714343235)
                    ·
                      rfl

theorem cell23_7286021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_7286021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286021 prefixEnd_7286021 := by exact prefixLift 7286021
  have htrace : WordTrace (prefixWord ++ tailWord_7286021) baseStart_7286021 baseEnd_7286021 := by
    simpa [prefixWord, tailWord_7286021, baseEnd_7286021] using wordTrace_append hprefix tailTrace_7286021
  have hstable : (prefixWord ++ tailWord_7286021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286021).length < 2 ^ (prefixWord ++ tailWord_7286021).sum := by decide
  have hdescent : baseEnd_7286021 < baseStart_7286021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286041 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_7286041 : Nat := 118140960795 + 7286041 * 2 ^ 59
def prefixEnd_7286041 : Nat := 4983230072969 + 3 ^ 40 * 7286041 * 2
def baseEnd_7286041 : Nat := 3741241101365433064779613

theorem tailTrace_7286041 : CollatzResearch.WordTrace tailWord_7286041 prefixEnd_7286041 3741241101365433064779613 := by
  unfold tailWord_7286041
  simp only [CollatzResearch.WordTrace]
  refine ⟨265743746996925288579609977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177162497997950192386406651 265743746996925288579609977)
  ·
    refine ⟨199307810247693966434707483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265743746996925288579609977 199307810247693966434707483)
    ·
      refine ⟨298961715371540949652061225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199307810247693966434707483 298961715371540949652061225)
      ·
        refine ⟨224221286528655712239045919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298961715371540949652061225 224221286528655712239045919)
        ·
          refine ⟨336331929792983568358568879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224221286528655712239045919 336331929792983568358568879)
          ·
            refine ⟨504497894689475352537853319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336331929792983568358568879 504497894689475352537853319)
            ·
              refine ⟨756746842034213028806779979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504497894689475352537853319 756746842034213028806779979)
              ·
                refine ⟨1135120263051319543210169969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756746842034213028806779979 1135120263051319543210169969)
                ·
                  refine ⟨851340197288489657407627477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135120263051319543210169969 851340197288489657407627477)
                  ·
                    refine ⟨19953285873948976345491269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 851340197288489657407627477 19953285873948976345491269)
                    ·
                      refine ⟨3741241101365433064779613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19953285873948976345491269 3741241101365433064779613)
                      ·
                        rfl

theorem cell23_7286041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_7286041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286041 prefixEnd_7286041 := by exact prefixLift 7286041
  have htrace : WordTrace (prefixWord ++ tailWord_7286041) baseStart_7286041 baseEnd_7286041 := by
    simpa [prefixWord, tailWord_7286041, baseEnd_7286041] using wordTrace_append hprefix tailTrace_7286041
  have hstable : (prefixWord ++ tailWord_7286041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286041).length < 2 ^ (prefixWord ++ tailWord_7286041).sum := by decide
  have hdescent : baseEnd_7286041 < baseStart_7286041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286042 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_7286042 : Nat := 118140960795 + 7286042 * 2 ^ 59
def prefixEnd_7286042 : Nat := 4983230072969 + 3 ^ 40 * 7286042 * 2
def baseEnd_7286042 : Nat := 415693512760676395651901

theorem tailTrace_7286042 : CollatzResearch.WordTrace tailWord_7286042 prefixEnd_7286042 415693512760676395651901 := by
  unfold tailWord_7286042
  simp only [CollatzResearch.WordTrace]
  refine ⟨66435945867480416437599095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177162522313281110500264253 66435945867480416437599095)
  ·
    refine ⟨99653918801220624656398643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66435945867480416437599095 99653918801220624656398643)
    ·
      refine ⟨149480878201830936984597965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99653918801220624656398643 149480878201830936984597965)
      ·
        refine ⟨56055329325686601369224237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149480878201830936984597965 56055329325686601369224237)
        ·
          refine ⟨21020748497132475513459089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56055329325686601369224237 21020748497132475513459089)
          ·
            refine ⟨15765561372849356635094317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21020748497132475513459089 15765561372849356635094317)
            ·
              refine ⟨5912085514818508738160369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15765561372849356635094317 5912085514818508738160369)
              ·
                refine ⟨4434064136113881553620277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912085514818508738160369 4434064136113881553620277)
                ·
                  refine ⟨415693512760676395651901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4434064136113881553620277 415693512760676395651901)
                  ·
                    rfl

theorem cell23_7286042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_7286042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286042 prefixEnd_7286042 := by exact prefixLift 7286042
  have htrace : WordTrace (prefixWord ++ tailWord_7286042) baseStart_7286042 baseEnd_7286042 := by
    simpa [prefixWord, tailWord_7286042, baseEnd_7286042] using wordTrace_append hprefix tailTrace_7286042
  have hstable : (prefixWord ++ tailWord_7286042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286042).length < 2 ^ (prefixWord ++ tailWord_7286042).sum := by decide
  have hdescent : baseEnd_7286042 < baseStart_7286042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286071 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_7286071 : Nat := 118140960795 + 7286071 * 2 ^ 59
def prefixEnd_7286071 : Nat := 4983230072969 + 3 ^ 40 * 7286071 * 2
def baseEnd_7286071 : Nat := 3741256505785067947404475

theorem tailTrace_7286071 : CollatzResearch.WordTrace tailWord_7286071 prefixEnd_7286071 3741256505785067947404475 := by
  unfold tailWord_7286071
  simp only [CollatzResearch.WordTrace]
  refine ⟨265744841186816603703202067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177163227457877735802134711 265744841186816603703202067)
  ·
    refine ⟨398617261780224905554803101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265744841186816603703202067 398617261780224905554803101)
    ·
      refine ⟨149481473167584339583051163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398617261780224905554803101 149481473167584339583051163)
      ·
        refine ⟨224222209751376509374576745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149481473167584339583051163 224222209751376509374576745)
        ·
          refine ⟨168166657313532382030932559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224222209751376509374576745 168166657313532382030932559)
          ·
            refine ⟨252249985970298573046398839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168166657313532382030932559 252249985970298573046398839)
            ·
              refine ⟨378374978955447859569598259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252249985970298573046398839 378374978955447859569598259)
              ·
                refine ⟨567562468433171789354397389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378374978955447859569598259 567562468433171789354397389)
                ·
                  refine ⟨212835925662439421007899021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567562468433171789354397389 212835925662439421007899021)
                  ·
                    refine ⟨79813472123414782877962133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212835925662439421007899021 79813472123414782877962133)
                    ·
                      refine ⟨3741256505785067947404475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79813472123414782877962133 3741256505785067947404475)
                      ·
                        rfl

theorem cell23_7286071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_7286071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286071 prefixEnd_7286071 := by exact prefixLift 7286071
  have htrace : WordTrace (prefixWord ++ tailWord_7286071) baseStart_7286071 baseEnd_7286071 := by
    simpa [prefixWord, tailWord_7286071, baseEnd_7286071] using wordTrace_append hprefix tailTrace_7286071
  have hstable : (prefixWord ++ tailWord_7286071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286071).length < 2 ^ (prefixWord ++ tailWord_7286071).sum := by decide
  have hdescent : baseEnd_7286071 < baseStart_7286071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286093 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 5]
def baseStart_7286093 : Nat := 118140960795 + 7286093 * 2 ^ 59
def prefixEnd_7286093 : Nat := 4983230072969 + 3 ^ 40 * 7286093 * 2
def baseEnd_7286093 : Nat := 415696422484385206814375

theorem tailTrace_7286093 : CollatzResearch.WordTrace tailWord_7286093 prefixEnd_7286093 415696422484385206814375 := by
  unfold tailWord_7286093
  simp only [CollatzResearch.WordTrace]
  refine ⟨265745643592736901460502933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177163762395157934307001955 265745643592736901460502933)
  ·
    refine ⟨12456827043409542255961075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265745643592736901460502933 12456827043409542255961075)
    ·
      refine ⟨18685240565114313383941613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12456827043409542255961075 18685240565114313383941613)
      ·
        refine ⟨7006965211917867518978105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18685240565114313383941613 7006965211917867518978105)
        ·
          refine ⟨5255223908938400639233579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7006965211917867518978105 5255223908938400639233579)
          ·
            refine ⟨7882835863407600958850369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255223908938400639233579 7882835863407600958850369)
            ·
              refine ⟨5912126897555700719137777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7882835863407600958850369 5912126897555700719137777)
              ·
                refine ⟨4434095173166775539353333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912126897555700719137777 4434095173166775539353333)
                ·
                  refine ⟨415696422484385206814375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4434095173166775539353333 415696422484385206814375)
                  ·
                    rfl

theorem cell23_7286093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_7286093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286093 prefixEnd_7286093 := by exact prefixLift 7286093
  have htrace : WordTrace (prefixWord ++ tailWord_7286093) baseStart_7286093 baseEnd_7286093 := by
    simpa [prefixWord, tailWord_7286093, baseEnd_7286093] using wordTrace_append hprefix tailTrace_7286093
  have hstable : (prefixWord ++ tailWord_7286093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286093).length < 2 ^ (prefixWord ++ tailWord_7286093).sum := by decide
  have hdescent : baseEnd_7286093 < baseStart_7286093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286126 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7286126 : Nat := 118140960795 + 7286126 * 2 ^ 59
def prefixEnd_7286126 : Nat := 4983230072969 + 3 ^ 40 * 7286126 * 2
def baseEnd_7286126 : Nat := 3741284747221065232216723

theorem tailTrace_7286126 : CollatzResearch.WordTrace tailWord_7286126 prefixEnd_7286126 3741284747221065232216723 := by
  unfold tailWord_7286126
  simp only [CollatzResearch.WordTrace]
  refine ⟨33218355900202168512056779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177164564801078232064302821 33218355900202168512056779)
  ·
    refine ⟨49827533850303252768085169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33218355900202168512056779 49827533850303252768085169)
    ·
      refine ⟨37370650387727439576063877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49827533850303252768085169 37370650387727439576063877)
      ·
        refine ⟨7006996947698894920511977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37370650387727439576063877 7006996947698894920511977)
        ·
          refine ⟨5255247710774171190383983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7006996947698894920511977 5255247710774171190383983)
          ·
            refine ⟨7882871566161256785575975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255247710774171190383983 7882871566161256785575975)
            ·
              refine ⟨11824307349241885178363963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7882871566161256785575975 11824307349241885178363963)
              ·
                refine ⟨17736461023862827767545945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11824307349241885178363963 17736461023862827767545945)
                ·
                  refine ⟨13302345767897120825659459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17736461023862827767545945 13302345767897120825659459)
                  ·
                    refine ⟨19953518651845681238489189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13302345767897120825659459 19953518651845681238489189)
                    ·
                      refine ⟨3741284747221065232216723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19953518651845681238489189 3741284747221065232216723)
                      ·
                        rfl

theorem cell23_7286126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7286126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286126 prefixEnd_7286126 := by exact prefixLift 7286126
  have htrace : WordTrace (prefixWord ++ tailWord_7286126) baseStart_7286126 baseEnd_7286126 := by
    simpa [prefixWord, tailWord_7286126, baseEnd_7286126] using wordTrace_append hprefix tailTrace_7286126
  have hstable : (prefixWord ++ tailWord_7286126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286126).length < 2 ^ (prefixWord ++ tailWord_7286126).sum := by decide
  have hdescent : baseEnd_7286126 < baseStart_7286126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286128 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_7286128 : Nat := 118140960795 + 7286128 * 2 ^ 59
def prefixEnd_7286128 : Nat := 4983230072969 + 3 ^ 40 * 7286128 * 2
def baseEnd_7286128 : Nat := 1247095258060791408130571

theorem tailTrace_7286128 : CollatzResearch.WordTrace tailWord_7286128 prefixEnd_7286128 1247095258060791408130571 := by
  unfold tailWord_7286128
  simp only [CollatzResearch.WordTrace]
  refine ⟨132873460073805051219013519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177164613431740068292018025 132873460073805051219013519)
  ·
    refine ⟨199310190110707576828520279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132873460073805051219013519 199310190110707576828520279)
    ·
      refine ⟨298965285166061365242780419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199310190110707576828520279 298965285166061365242780419)
      ·
        refine ⟨448447927749092047864170629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298965285166061365242780419 448447927749092047864170629)
        ·
          refine ⟨84083986452954758974531993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 448447927749092047864170629 84083986452954758974531993)
          ·
            refine ⟨63062989839716069230898995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84083986452954758974531993 63062989839716069230898995)
            ·
              refine ⟨94594484759574103846348493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63062989839716069230898995 94594484759574103846348493)
              ·
                refine ⟨35472931784840288942380685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94594484759574103846348493 35472931784840288942380685)
                ·
                  refine ⟨13302349419315108353392757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35472931784840288942380685 13302349419315108353392757)
                  ·
                    refine ⟨1247095258060791408130571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13302349419315108353392757 1247095258060791408130571)
                    ·
                      rfl

theorem cell23_7286128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_7286128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286128 prefixEnd_7286128 := by exact prefixLift 7286128
  have htrace : WordTrace (prefixWord ++ tailWord_7286128) baseStart_7286128 baseEnd_7286128 := by
    simpa [prefixWord, tailWord_7286128, baseEnd_7286128] using wordTrace_append hprefix tailTrace_7286128
  have hstable : (prefixWord ++ tailWord_7286128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286128).length < 2 ^ (prefixWord ++ tailWord_7286128).sum := by decide
  have hdescent : baseEnd_7286128 < baseStart_7286128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286135 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 1, 5, 2]
def baseStart_7286135 : Nat := 118140960795 + 7286135 * 2 ^ 59
def prefixEnd_7286135 : Nat := 4983230072969 + 3 ^ 40 * 7286135 * 2
def baseEnd_7286135 : Nat := 3741289368546955697004181

theorem tailTrace_7286135 : CollatzResearch.WordTrace tailWord_7286135 prefixEnd_7286135 3741289368546955697004181 := by
  unfold tailWord_7286135
  simp only [CollatzResearch.WordTrace]
  refine ⟨265747175458584742633531859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177164783639056495089021239 265747175458584742633531859)
  ·
    refine ⟨398620763187877113950297789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265747175458584742633531859 398620763187877113950297789)
    ·
      refine ⟨149482786195453917731361671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398620763187877113950297789 149482786195453917731361671)
      ·
        refine ⟨224224179293180876597042507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149482786195453917731361671 224224179293180876597042507)
        ·
          refine ⟨336336268939771314895563761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224224179293180876597042507 336336268939771314895563761)
          ·
            refine ⟨252252201704828486171672821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336336268939771314895563761 252252201704828486171672821)
            ·
              refine ⟨23648643909827670578594327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252252201704828486171672821 23648643909827670578594327)
              ·
                refine ⟨35472965864741505867891491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23648643909827670578594327 35472965864741505867891491)
                ·
                  refine ⟨53209448797112258801837237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35472965864741505867891491 53209448797112258801837237)
                  ·
                    refine ⟨4988385824729274262672241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53209448797112258801837237 4988385824729274262672241)
                    ·
                      refine ⟨3741289368546955697004181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988385824729274262672241 3741289368546955697004181)
                      ·
                        rfl

theorem cell23_7286135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_7286135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286135 prefixEnd_7286135 := by exact prefixLift 7286135
  have htrace : WordTrace (prefixWord ++ tailWord_7286135) baseStart_7286135 baseEnd_7286135 := by
    simpa [prefixWord, tailWord_7286135, baseEnd_7286135] using wordTrace_append hprefix tailTrace_7286135
  have hstable : (prefixWord ++ tailWord_7286135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286135).length < 2 ^ (prefixWord ++ tailWord_7286135).sum := by decide
  have hdescent : baseEnd_7286135 < baseStart_7286135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286175 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 1, 6]
def baseStart_7286175 : Nat := 118140960795 + 7286175 * 2 ^ 59
def prefixEnd_7286175 : Nat := 4983230072969 + 3 ^ 40 * 7286175 * 2
def baseEnd_7286175 : Nat := 1247103302591045180167999

theorem tailTrace_7286175 : CollatzResearch.WordTrace tailWord_7286175 prefixEnd_7286175 1247103302591045180167999 := by
  unfold tailWord_7286175
  simp only [CollatzResearch.WordTrace]
  refine ⟨265748634378439829464987979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177165756252293219643325319 265748634378439829464987979)
  ·
    refine ⟨398622951567659744197481969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265748634378439829464987979 398622951567659744197481969)
    ·
      refine ⟨298967213675744808148111477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398622951567659744197481969 298967213675744808148111477)
      ·
        refine ⟨28028176282101075763885451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298967213675744808148111477 28028176282101075763885451)
        ·
          refine ⟨42042264423151613645828177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28028176282101075763885451 42042264423151613645828177)
          ·
            refine ⟨31531698317363710234371133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42042264423151613645828177 31531698317363710234371133)
            ·
              refine ⟨11824386869011391337889175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31531698317363710234371133 11824386869011391337889175)
              ·
                refine ⟨17736580303517087006833763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11824386869011391337889175 17736580303517087006833763)
                ·
                  refine ⟨26604870455275630510250645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17736580303517087006833763 26604870455275630510250645)
                  ·
                    refine ⟨1247103302591045180167999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26604870455275630510250645 1247103302591045180167999)
                    ·
                      rfl

theorem cell23_7286175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_7286175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286175 prefixEnd_7286175 := by exact prefixLift 7286175
  have htrace : WordTrace (prefixWord ++ tailWord_7286175) baseStart_7286175 baseEnd_7286175 := by
    simpa [prefixWord, tailWord_7286175, baseEnd_7286175] using wordTrace_append hprefix tailTrace_7286175
  have hstable : (prefixWord ++ tailWord_7286175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286175).length < 2 ^ (prefixWord ++ tailWord_7286175).sum := by decide
  have hdescent : baseEnd_7286175 < baseStart_7286175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286225 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 9, 2]
def baseStart_7286225 : Nat := 118140960795 + 7286225 * 2 ^ 59
def prefixEnd_7286225 : Nat := 4983230072969 + 3 ^ 40 * 7286225 * 2
def baseEnd_7286225 : Nat := 3741335581805860344878767

theorem tailTrace_7286225 : CollatzResearch.WordTrace tailWord_7286225 prefixEnd_7286225 3741335581805860344878767 := by
  unfold tailWord_7286225
  simp only [CollatzResearch.WordTrace]
  refine ⟨265750458028258688004308129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177166972018839125336205419 265750458028258688004308129)
  ·
    refine ⟨199312843521194016003231097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265750458028258688004308129 199312843521194016003231097)
    ·
      refine ⟨149484632640895512002423323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199312843521194016003231097 149484632640895512002423323)
      ·
        refine ⟨224226948961343268003634985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149484632640895512002423323 224226948961343268003634985)
        ·
          refine ⟨168170211721007451002726239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224226948961343268003634985 168170211721007451002726239)
          ·
            refine ⟨252255317581511176504089359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168170211721007451002726239 252255317581511176504089359)
            ·
              refine ⟨378382976372266764756134039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252255317581511176504089359 378382976372266764756134039)
              ·
                refine ⟨567574464558400147134201059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378382976372266764756134039 567574464558400147134201059)
                ·
                  refine ⟨851361696837600220701301589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567574464558400147134201059 851361696837600220701301589)
                  ·
                    refine ⟨4988447442407813793171689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 851361696837600220701301589 4988447442407813793171689)
                    ·
                      refine ⟨3741335581805860344878767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988447442407813793171689 3741335581805860344878767)
                      ·
                        rfl

theorem cell23_7286225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_7286225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286225 prefixEnd_7286225 := by exact prefixLift 7286225
  have htrace : WordTrace (prefixWord ++ tailWord_7286225) baseStart_7286225 baseEnd_7286225 := by
    simpa [prefixWord, tailWord_7286225, baseEnd_7286225] using wordTrace_append hprefix tailTrace_7286225
  have hstable : (prefixWord ++ tailWord_7286225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286225).length < 2 ^ (prefixWord ++ tailWord_7286225).sum := by decide
  have hdescent : baseEnd_7286225 < baseStart_7286225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286289 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 2, 2, 2]
def baseStart_7286289 : Nat := 118140960795 + 7286289 * 2 ^ 59
def prefixEnd_7286289 : Nat := 4983230072969 + 3 ^ 40 * 7286289 * 2
def baseEnd_7286289 : Nat := 3741368444567748094478473

theorem tailTrace_7286289 : CollatzResearch.WordTrace tailWord_7286289 prefixEnd_7286289 3741368444567748094478473 := by
  unfold tailWord_7286289
  simp only [CollatzResearch.WordTrace]
  refine ⟨265752792300026826934637921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177168528200017884623091947 265752792300026826934637921)
  ·
    refine ⟨199314594225020120200978441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265752792300026826934637921 199314594225020120200978441)
    ·
      refine ⟨149485945668765090150733831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199314594225020120200978441 149485945668765090150733831)
      ·
        refine ⟨224228918503147635226100747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149485945668765090150733831 224228918503147635226100747)
        ·
          refine ⟨336343377754721452839151121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224228918503147635226100747 336343377754721452839151121)
          ·
            refine ⟨252257533316041089629363341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336343377754721452839151121 252257533316041089629363341)
            ·
              refine ⟨94596574993515408611011253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252257533316041089629363341 94596574993515408611011253)
              ·
                refine ⟨8868428905642069557282305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94596574993515408611011253 8868428905642069557282305)
                ·
                  refine ⟨6651321679231552167961729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8868428905642069557282305 6651321679231552167961729)
                  ·
                    refine ⟨4988491259423664125971297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651321679231552167961729 4988491259423664125971297)
                    ·
                      refine ⟨3741368444567748094478473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988491259423664125971297 3741368444567748094478473)
                      ·
                        rfl

theorem cell23_7286289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_7286289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286289 prefixEnd_7286289 := by exact prefixLift 7286289
  have htrace : WordTrace (prefixWord ++ tailWord_7286289) baseStart_7286289 baseEnd_7286289 := by
    simpa [prefixWord, tailWord_7286289, baseEnd_7286289] using wordTrace_append hprefix tailTrace_7286289
  have hstable : (prefixWord ++ tailWord_7286289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286289).length < 2 ^ (prefixWord ++ tailWord_7286289).sum := by decide
  have hdescent : baseEnd_7286289 < baseStart_7286289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286362 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2]
def baseStart_7286362 : Nat := 118140960795 + 7286362 * 2 ^ 59
def prefixEnd_7286362 : Nat := 4983230072969 + 3 ^ 40 * 7286362 * 2
def baseEnd_7286362 : Nat := 3741405928655526308865637

theorem tailTrace_7286362 : CollatzResearch.WordTrace tailWord_7286362 prefixEnd_7286362 3741405928655526308865637 := by
  unfold tailWord_7286362
  simp only [CollatzResearch.WordTrace]
  refine ⟨66438863707190590100511335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177170303219174906934696893 66438863707190590100511335)
  ·
    refine ⟨99658295560785885150767003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66438863707190590100511335 99658295560785885150767003)
    ·
      refine ⟨149487443341178827726150505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99658295560785885150767003 149487443341178827726150505)
      ·
        refine ⟨112115582505884120794612879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149487443341178827726150505 112115582505884120794612879)
        ·
          refine ⟨168173373758826181191919319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112115582505884120794612879 168173373758826181191919319)
          ·
            refine ⟨252260060638239271787878979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168173373758826181191919319 252260060638239271787878979)
            ·
              refine ⟨378390090957358907681818469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252260060638239271787878979 378390090957358907681818469)
              ·
                refine ⟨70948142054504795190340963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378390090957358907681818469 70948142054504795190340963)
                ·
                  refine ⟨106422213081757192785511445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70948142054504795190340963 106422213081757192785511445)
                  ·
                    refine ⟨4988541238207368411820849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106422213081757192785511445 4988541238207368411820849)
                    ·
                      refine ⟨3741405928655526308865637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988541238207368411820849 3741405928655526308865637)
                      ·
                        rfl

theorem cell23_7286362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_7286362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286362 prefixEnd_7286362 := by exact prefixLift 7286362
  have htrace : WordTrace (prefixWord ++ tailWord_7286362) baseStart_7286362 baseEnd_7286362 := by
    simpa [prefixWord, tailWord_7286362, baseEnd_7286362] using wordTrace_append hprefix tailTrace_7286362
  have hstable : (prefixWord ++ tailWord_7286362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286362).length < 2 ^ (prefixWord ++ tailWord_7286362).sum := by decide
  have hdescent : baseEnd_7286362 < baseStart_7286362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286375 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_7286375 : Nat := 118140960795 + 7286375 * 2 ^ 59
def prefixEnd_7286375 : Nat := 4983230072969 + 3 ^ 40 * 7286375 * 2
def baseEnd_7286375 : Nat := 3741412603904034758003077

theorem tailTrace_7286375 : CollatzResearch.WordTrace tailWord_7286375 prefixEnd_7286375 3741412603904034758003077 := by
  unfold tailWord_7286375
  simp only [CollatzResearch.WordTrace]
  refine ⟨265755928977715263622268579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177170619318476842414845719 265755928977715263622268579)
  ·
    refine ⟨398633893466572895433402869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265755928977715263622268579 398633893466572895433402869)
    ·
      refine ⟨37371927512491208946881519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 398633893466572895433402869 37371927512491208946881519)
      ·
        refine ⟨56057891268736813420322279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37371927512491208946881519 56057891268736813420322279)
        ·
          refine ⟨84086836903105220130483419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56057891268736813420322279 84086836903105220130483419)
          ·
            refine ⟨126130255354657830195725129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84086836903105220130483419 126130255354657830195725129)
            ·
              refine ⟨94597691515993372646793847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126130255354657830195725129 94597691515993372646793847)
              ·
                refine ⟨141896537273990058970190771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94597691515993372646793847 141896537273990058970190771)
                ·
                  refine ⟨212844805910985088455286157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141896537273990058970190771 212844805910985088455286157)
                  ·
                    refine ⟨79816802216619408170732309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212844805910985088455286157 79816802216619408170732309)
                    ·
                      refine ⟨3741412603904034758003077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79816802216619408170732309 3741412603904034758003077)
                      ·
                        rfl

theorem cell23_7286375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_7286375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286375 prefixEnd_7286375 := by exact prefixLift 7286375
  have htrace : WordTrace (prefixWord ++ tailWord_7286375) baseStart_7286375 baseEnd_7286375 := by
    simpa [prefixWord, tailWord_7286375, baseEnd_7286375] using wordTrace_append hprefix tailTrace_7286375
  have hstable : (prefixWord ++ tailWord_7286375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286375).length < 2 ^ (prefixWord ++ tailWord_7286375).sum := by decide
  have hdescent : baseEnd_7286375 < baseStart_7286375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286425 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_7286425 : Nat := 118140960795 + 7286425 * 2 ^ 59
def prefixEnd_7286425 : Nat := 4983230072969 + 3 ^ 40 * 7286425 * 2
def baseEnd_7286425 : Nat := 3741438277936759562377847

theorem tailTrace_7286425 : CollatzResearch.WordTrace tailWord_7286425 prefixEnd_7286425 3741438277936759562377847 := by
  unfold tailWord_7286425
  simp only [CollatzResearch.WordTrace]
  refine ⟨265757752627534122161588729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177171835085022748107725819 265757752627534122161588729)
  ·
    refine ⟨199318314470650591621191547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265757752627534122161588729 199318314470650591621191547)
    ·
      refine ⟨298977471705975887431787321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199318314470650591621191547 298977471705975887431787321)
      ·
        refine ⟨224233103779481915573840491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298977471705975887431787321 224233103779481915573840491)
        ·
          refine ⟨336349655669222873360760737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224233103779481915573840491 336349655669222873360760737)
          ·
            refine ⟨252262241751917155020570553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336349655669222873360760737 252262241751917155020570553)
            ·
              refine ⟨189196681313937866265427915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252262241751917155020570553 189196681313937866265427915)
              ·
                refine ⟨283795021970906799398141873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189196681313937866265427915 283795021970906799398141873)
                ·
                  refine ⟨212846266478180099548606405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283795021970906799398141873 212846266478180099548606405)
                  ·
                    refine ⟨39908674964658768665363701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212846266478180099548606405 39908674964658768665363701)
                    ·
                      refine ⟨3741438277936759562377847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39908674964658768665363701 3741438277936759562377847)
                      ·
                        rfl

theorem cell23_7286425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_7286425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286425 prefixEnd_7286425 := by exact prefixLift 7286425
  have htrace : WordTrace (prefixWord ++ tailWord_7286425) baseStart_7286425 baseEnd_7286425 := by
    simpa [prefixWord, tailWord_7286425, baseEnd_7286425] using wordTrace_append hprefix tailTrace_7286425
  have hstable : (prefixWord ++ tailWord_7286425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286425).length < 2 ^ (prefixWord ++ tailWord_7286425).sum := by decide
  have hdescent : baseEnd_7286425 < baseStart_7286425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286475 : List Nat := [1, 1, 1, 1, 3, 2, 1, 13]
def baseStart_7286475 : Nat := 118140960795 + 7286475 * 2 ^ 59
def prefixEnd_7286475 : Nat := 4983230072969 + 3 ^ 40 * 7286475 * 2
def baseEnd_7286475 : Nat := 138572738961832754324171

theorem tailTrace_7286475 : CollatzResearch.WordTrace tailWord_7286475 prefixEnd_7286475 138572738961832754324171 := by
  unfold tailWord_7286475
  simp only [CollatzResearch.WordTrace]
  refine ⟨265759576277352980700908879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177173050851568653800605919 265759576277352980700908879)
  ·
    refine ⟨398639364416029471051363319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265759576277352980700908879 398639364416029471051363319)
    ·
      refine ⟨597959046624044206577044979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398639364416029471051363319 597959046624044206577044979)
      ·
        refine ⟨896938569936066309865567469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597959046624044206577044979 896938569936066309865567469)
        ·
          refine ⟨336351963726024866199587801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 896938569936066309865567469 336351963726024866199587801)
          ·
            refine ⟨252263972794518649649690851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336351963726024866199587801 252263972794518649649690851)
            ·
              refine ⟨378395959191777974474536277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252263972794518649649690851 378395959191777974474536277)
              ·
                refine ⟨138572738961832754324171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 378395959191777974474536277 138572738961832754324171)
                ·
                  rfl

theorem cell23_7286475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 13].length) (baseStart_7286475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286475 prefixEnd_7286475 := by exact prefixLift 7286475
  have htrace : WordTrace (prefixWord ++ tailWord_7286475) baseStart_7286475 baseEnd_7286475 := by
    simpa [prefixWord, tailWord_7286475, baseEnd_7286475] using wordTrace_append hprefix tailTrace_7286475
  have hstable : (prefixWord ++ tailWord_7286475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286475).length < 2 ^ (prefixWord ++ tailWord_7286475).sum := by decide
  have hdescent : baseEnd_7286475 < baseStart_7286475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286519 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_7286519 : Nat := 118140960795 + 7286519 * 2 ^ 59
def prefixEnd_7286519 : Nat := 4983230072969 + 3 ^ 40 * 7286519 * 2
def baseEnd_7286519 : Nat := 3741486545118282194602415

theorem tailTrace_7286519 : CollatzResearch.WordTrace tailWord_7286519 prefixEnd_7286519 3741486545118282194602415 := by
  unfold tailWord_7286519
  simp only [CollatzResearch.WordTrace]
  refine ⟨265761181089193576215510611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177174120726129050810340407 265761181089193576215510611)
  ·
    refine ⟨398641771633790364323265917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265761181089193576215510611 398641771633790364323265917)
    ·
      refine ⟨149490664362671386621224719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398641771633790364323265917 149490664362671386621224719)
      ·
        refine ⟨224235996544007079931837079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149490664362671386621224719 224235996544007079931837079)
        ·
          refine ⟨336353994816010619897755619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224235996544007079931837079 336353994816010619897755619)
          ·
            refine ⟨504530992224015929846633429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336353994816010619897755619 504530992224015929846633429)
            ·
              refine ⟨11824945130250373355780471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 504530992224015929846633429 11824945130250373355780471)
              ·
                refine ⟨17737417695375560033670707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11824945130250373355780471 17737417695375560033670707)
                ·
                  refine ⟨26606126543063340050506061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17737417695375560033670707 26606126543063340050506061)
                  ·
                    refine ⟨9977297453648752518939773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26606126543063340050506061 9977297453648752518939773)
                    ·
                      refine ⟨3741486545118282194602415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9977297453648752518939773 3741486545118282194602415)
                      ·
                        rfl

theorem cell23_7286519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_7286519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286519 prefixEnd_7286519 := by exact prefixLift 7286519
  have htrace : WordTrace (prefixWord ++ tailWord_7286519) baseStart_7286519 baseEnd_7286519 := by
    simpa [prefixWord, tailWord_7286519, baseEnd_7286519] using wordTrace_append hprefix tailTrace_7286519
  have hstable : (prefixWord ++ tailWord_7286519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286519).length < 2 ^ (prefixWord ++ tailWord_7286519).sum := by decide
  have hdescent : baseEnd_7286519 < baseStart_7286519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286552 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_7286552 : Nat := 118140960795 + 7286552 * 2 ^ 59
def prefixEnd_7286552 : Nat := 4983230072969 + 3 ^ 40 * 7286552 * 2
def baseEnd_7286552 : Nat := 1247167829993293521829921

theorem tailTrace_7286552 : CollatzResearch.WordTrace tailWord_7286552 prefixEnd_7286552 1247167829993293521829921 := by
  unfold tailWord_7286552
  simp only [CollatzResearch.WordTrace]
  refine ⟨132881192349037011425730955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177174923132049348567641273 132881192349037011425730955)
  ·
    refine ⟨199321788523555517138596433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132881192349037011425730955 199321788523555517138596433)
    ·
      refine ⟨149491341392666637853947325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199321788523555517138596433 149491341392666637853947325)
      ·
        refine ⟨56059253022249989195230247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149491341392666637853947325 56059253022249989195230247)
        ·
          refine ⟨84088879533374983792845371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56059253022249989195230247 84088879533374983792845371)
          ·
            refine ⟨126133319300062475689268057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84088879533374983792845371 126133319300062475689268057)
            ·
              refine ⟨94599989475046856766951043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126133319300062475689268057 94599989475046856766951043)
              ·
                refine ⟨141899984212570285150426565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94599989475046856766951043 141899984212570285150426565)
                ·
                  refine ⟨26606247039856928465704981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141899984212570285150426565 26606247039856928465704981)
                  ·
                    refine ⟨1247167829993293521829921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26606247039856928465704981 1247167829993293521829921)
                    ·
                      rfl

theorem cell23_7286552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_7286552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286552 prefixEnd_7286552 := by exact prefixLift 7286552
  have htrace : WordTrace (prefixWord ++ tailWord_7286552) baseStart_7286552 baseEnd_7286552 := by
    simpa [prefixWord, tailWord_7286552, baseEnd_7286552] using wordTrace_append hprefix tailTrace_7286552
  have hstable : (prefixWord ++ tailWord_7286552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286552).length < 2 ^ (prefixWord ++ tailWord_7286552).sum := by decide
  have hdescent : baseEnd_7286552 < baseStart_7286552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286580 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7286580 : Nat := 118140960795 + 7286580 * 2 ^ 59
def prefixEnd_7286580 : Nat := 4983230072969 + 3 ^ 40 * 7286580 * 2
def baseEnd_7286580 : Nat := 3741517867438206455939635

theorem tailTrace_7286580 : CollatzResearch.WordTrace tailWord_7286580 prefixEnd_7286580 3741517867438206455939635 := by
  unfold tailWord_7286580
  simp only [CollatzResearch.WordTrace]
  refine ⟨132881702970986291816740597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177175603961315055755654129 132881702970986291816740597)
  ·
    refine ⟨12457659653529964857819431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132881702970986291816740597 12457659653529964857819431)
    ·
      refine ⟨18686489480294947286729147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457659653529964857819431 18686489480294947286729147)
      ·
        refine ⟨28029734220442420930093721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18686489480294947286729147 28029734220442420930093721)
        ·
          refine ⟨21022300665331815697570291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28029734220442420930093721 21022300665331815697570291)
          ·
            refine ⟨31533450997997723546355437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21022300665331815697570291 31533450997997723546355437)
            ·
              refine ⟨11825044124249146329883289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31533450997997723546355437 11825044124249146329883289)
              ·
                refine ⟨8868783093186859747412467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11825044124249146329883289 8868783093186859747412467)
                ·
                  refine ⟨13303174639780289621118701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8868783093186859747412467 13303174639780289621118701)
                  ·
                    refine ⟨4988690489917608607919513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13303174639780289621118701 4988690489917608607919513)
                    ·
                      refine ⟨3741517867438206455939635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988690489917608607919513 3741517867438206455939635)
                      ·
                        rfl

theorem cell23_7286580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7286580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286580 prefixEnd_7286580 := by exact prefixLift 7286580
  have htrace : WordTrace (prefixWord ++ tailWord_7286580) baseStart_7286580 baseEnd_7286580 := by
    simpa [prefixWord, tailWord_7286580, baseEnd_7286580] using wordTrace_append hprefix tailTrace_7286580
  have hstable : (prefixWord ++ tailWord_7286580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286580).length < 2 ^ (prefixWord ++ tailWord_7286580).sum := by decide
  have hdescent : baseEnd_7286580 < baseStart_7286580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286610 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_7286610 : Nat := 118140960795 + 7286610 * 2 ^ 59
def prefixEnd_7286610 : Nat := 4983230072969 + 3 ^ 40 * 7286610 * 2
def baseEnd_7286610 : Nat := 3741533271857841338564497

theorem tailTrace_7286610 : CollatzResearch.WordTrace tailWord_7286610 prefixEnd_7286610 3741533271857841338564497 := by
  unfold tailWord_7286610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66441125032965974689268321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177176333421242599171382189 66441125032965974689268321)
  ·
    refine ⟨49830843774724481016951241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66441125032965974689268321 49830843774724481016951241)
    ·
      refine ⟨37373132831043360762713431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49830843774724481016951241 37373132831043360762713431)
      ·
        refine ⟨56059699246565041144070147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37373132831043360762713431 56059699246565041144070147)
        ·
          refine ⟨84089548869847561716105221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56059699246565041144070147 84089548869847561716105221)
          ·
            refine ⟨15766790413096417821769729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84089548869847561716105221 15766790413096417821769729)
            ·
              refine ⟨11825092809822313366327297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15766790413096417821769729 11825092809822313366327297)
              ·
                refine ⟨8868819607366735024745473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11825092809822313366327297 8868819607366735024745473)
                ·
                  refine ⟨6651614705525051268559105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8868819607366735024745473 6651614705525051268559105)
                  ·
                    refine ⟨4988711029143788451419329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651614705525051268559105 4988711029143788451419329)
                    ·
                      refine ⟨3741533271857841338564497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988711029143788451419329 3741533271857841338564497)
                      ·
                        rfl

theorem cell23_7286610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_7286610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286610 prefixEnd_7286610 := by exact prefixLift 7286610
  have htrace : WordTrace (prefixWord ++ tailWord_7286610) baseStart_7286610 baseEnd_7286610 := by
    simpa [prefixWord, tailWord_7286610, baseEnd_7286610] using wordTrace_append hprefix tailTrace_7286610
  have hstable : (prefixWord ++ tailWord_7286610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286610).length < 2 ^ (prefixWord ++ tailWord_7286610).sum := by decide
  have hdescent : baseEnd_7286610 < baseStart_7286610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286626 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7286626 : Nat := 118140960795 + 7286626 * 2 ^ 59
def prefixEnd_7286626 : Nat := 4983230072969 + 3 ^ 40 * 7286626 * 2
def baseEnd_7286626 : Nat := 3741541487548313275964423

theorem tailTrace_7286626 : CollatzResearch.WordTrace tailWord_7286626 prefixEnd_7286626 3741541487548313275964423 := by
  unfold tailWord_7286626
  simp only [CollatzResearch.WordTrace]
  refine ⟨66441270924951483372413933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177176722466537288993103821 66441270924951483372413933)
  ·
    refine ⟨24915476596856806264655225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66441270924951483372413933 24915476596856806264655225)
    ·
      refine ⟨18686607447642604698491419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24915476596856806264655225 18686607447642604698491419)
      ·
        refine ⟨28029911171463907047737129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18686607447642604698491419 28029911171463907047737129)
        ·
          refine ⟨21022433378597930285802847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28029911171463907047737129 21022433378597930285802847)
          ·
            refine ⟨31533650067896895428704271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21022433378597930285802847 31533650067896895428704271)
            ·
              refine ⟨47300475101845343143056407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31533650067896895428704271 47300475101845343143056407)
              ·
                refine ⟨70950712652768014714584611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47300475101845343143056407 70950712652768014714584611)
                ·
                  refine ⟨106426068979152022071876917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70950712652768014714584611 106426068979152022071876917)
                  ·
                    refine ⟨9977443966795502069238461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106426068979152022071876917 9977443966795502069238461)
                    ·
                      refine ⟨3741541487548313275964423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9977443966795502069238461 3741541487548313275964423)
                      ·
                        rfl

theorem cell23_7286626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7286626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286626 prefixEnd_7286626 := by exact prefixLift 7286626
  have htrace : WordTrace (prefixWord ++ tailWord_7286626) baseStart_7286626 baseEnd_7286626 := by
    simpa [prefixWord, tailWord_7286626, baseEnd_7286626] using wordTrace_append hprefix tailTrace_7286626
  have hstable : (prefixWord ++ tailWord_7286626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286626).length < 2 ^ (prefixWord ++ tailWord_7286626).sum := by decide
  have hdescent : baseEnd_7286626 < baseStart_7286626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286649 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7286649 : Nat := 118140960795 + 7286649 * 2 ^ 59
def prefixEnd_7286649 : Nat := 4983230072969 + 3 ^ 40 * 7286649 * 2
def baseEnd_7286649 : Nat := 3741553297603366685976817

theorem tailTrace_7286649 : CollatzResearch.WordTrace tailWord_7286649 prefixEnd_7286649 3741553297603366685976817 := by
  unfold tailWord_7286649
  simp only [CollatzResearch.WordTrace]
  refine ⟨265765922578722608417743001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177177281719148405611828667 265765922578722608417743001)
  ·
    refine ⟨199324441934041956313307251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265765922578722608417743001 199324441934041956313307251)
    ·
      refine ⟨298986662901062934469960877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199324441934041956313307251 298986662901062934469960877)
      ·
        refine ⟨112119998587898600426235329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298986662901062934469960877 112119998587898600426235329)
        ·
          refine ⟨84089998940923950319676497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112119998587898600426235329 84089998940923950319676497)
          ·
            refine ⟨63067499205692962739757373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84089998940923950319676497 63067499205692962739757373)
            ·
              refine ⟨23650312202134861027409015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63067499205692962739757373 23650312202134861027409015)
              ·
                refine ⟨35475468303202291541113523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23650312202134861027409015 35475468303202291541113523)
                ·
                  refine ⟨53213202454803437311670285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35475468303202291541113523 53213202454803437311670285)
                  ·
                    refine ⟨19954950920551288991876357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53213202454803437311670285 19954950920551288991876357)
                    ·
                      refine ⟨3741553297603366685976817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19954950920551288991876357 3741553297603366685976817)
                      ·
                        rfl

theorem cell23_7286649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7286649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286649 prefixEnd_7286649 := by exact prefixLift 7286649
  have htrace : WordTrace (prefixWord ++ tailWord_7286649) baseStart_7286649 baseEnd_7286649 := by
    simpa [prefixWord, tailWord_7286649, baseEnd_7286649] using wordTrace_append hprefix tailTrace_7286649
  have hstable : (prefixWord ++ tailWord_7286649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286649).length < 2 ^ (prefixWord ++ tailWord_7286649).sum := by decide
  have hdescent : baseEnd_7286649 < baseStart_7286649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286756 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_7286756 : Nat := 118140960795 + 7286756 * 2 ^ 59
def prefixEnd_7286756 : Nat := 4983230072969 + 3 ^ 40 * 7286756 * 2
def baseEnd_7286756 : Nat := 3741608240033397767338825

theorem tailTrace_7286756 : CollatzResearch.WordTrace tailWord_7286756 prefixEnd_7286756 3741608240033397767338825 := by
  unfold tailWord_7286756
  simp only [CollatzResearch.WordTrace]
  refine ⟨132884912594667482845944061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177179883459556643794592081 132884912594667482845944061)
  ·
    refine ⟨49831842223000306067229023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132884912594667482845944061 49831842223000306067229023)
    ·
      refine ⟨74747763334500459100843535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49831842223000306067229023 74747763334500459100843535)
      ·
        refine ⟨112121645001750688651265303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74747763334500459100843535 112121645001750688651265303)
        ·
          refine ⟨168182467502626032976897955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112121645001750688651265303 168182467502626032976897955)
          ·
            refine ⟨252273701253939049465346933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168182467502626032976897955 252273701253939049465346933)
            ·
              refine ⟨23650659492556785887376275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252273701253939049465346933 23650659492556785887376275)
              ·
                refine ⟨35475989238835178831064413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23650659492556785887376275 35475989238835178831064413)
                ·
                  refine ⟨13303495964563192061649155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35475989238835178831064413 13303495964563192061649155)
                  ·
                    refine ⟨19955243946844788092473733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13303495964563192061649155 19955243946844788092473733)
                    ·
                      refine ⟨3741608240033397767338825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19955243946844788092473733 3741608240033397767338825)
                      ·
                        rfl

theorem cell23_7286756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_7286756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286756 prefixEnd_7286756 := by exact prefixLift 7286756
  have htrace : WordTrace (prefixWord ++ tailWord_7286756) baseStart_7286756 baseEnd_7286756 := by
    simpa [prefixWord, tailWord_7286756, baseEnd_7286756] using wordTrace_append hprefix tailTrace_7286756
  have hstable : (prefixWord ++ tailWord_7286756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286756).length < 2 ^ (prefixWord ++ tailWord_7286756).sum := by decide
  have hdescent : baseEnd_7286756 < baseStart_7286756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286766 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7286766 : Nat := 118140960795 + 7286766 * 2 ^ 59
def prefixEnd_7286766 : Nat := 4983230072969 + 3 ^ 40 * 7286766 * 2
def baseEnd_7286766 : Nat := 1247204458279980909404593

theorem tailTrace_7286766 : CollatzResearch.WordTrace tailWord_7286766 prefixEnd_7286766 1247204458279980909404593 := by
  unfold tailWord_7286766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33221273739912342174969019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177180126612865824933168101 33221273739912342174969019)
  ·
    refine ⟨49831910609868513262453529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33221273739912342174969019 49831910609868513262453529)
    ·
      refine ⟨37373932957401384946840147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49831910609868513262453529 37373932957401384946840147)
      ·
        refine ⟨56060899436102077420260221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37373932957401384946840147 56060899436102077420260221)
        ·
          refine ⟨21022837288538279032597583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56060899436102077420260221 21022837288538279032597583)
          ·
            refine ⟨31534255932807418548896375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21022837288538279032597583 31534255932807418548896375)
            ·
              refine ⟨47301383899211127823344563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31534255932807418548896375 47301383899211127823344563)
              ·
                refine ⟨70952075848816691735016845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47301383899211127823344563 70952075848816691735016845)
                ·
                  refine ⟨26607028443306259400631317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70952075848816691735016845 26607028443306259400631317)
                  ·
                    refine ⟨1247204458279980909404593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26607028443306259400631317 1247204458279980909404593)
                    ·
                      rfl

theorem cell23_7286766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7286766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286766 prefixEnd_7286766 := by exact prefixLift 7286766
  have htrace : WordTrace (prefixWord ++ tailWord_7286766) baseStart_7286766 baseEnd_7286766 := by
    simpa [prefixWord, tailWord_7286766, baseEnd_7286766] using wordTrace_append hprefix tailTrace_7286766
  have hstable : (prefixWord ++ tailWord_7286766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286766).length < 2 ^ (prefixWord ++ tailWord_7286766).sum := by decide
  have hdescent : baseEnd_7286766 < baseStart_7286766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286776 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_7286776 : Nat := 118140960795 + 7286776 * 2 ^ 59
def prefixEnd_7286776 : Nat := 4983230072969 + 3 ^ 40 * 7286776 * 2
def baseEnd_7286776 : Nat := 3741618509646487689088733

theorem tailTrace_7286776 : CollatzResearch.WordTrace tailWord_7286776 prefixEnd_7286776 3741618509646487689088733 := by
  unfold tailWord_7286776
  simp only [CollatzResearch.WordTrace]
  refine ⟨132885277324631254553808091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177180369766175006071744121 132885277324631254553808091)
  ·
    refine ⟨199327915986946881830712137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132885277324631254553808091 199327915986946881830712137)
    ·
      refine ⟨149495936990210161373034103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199327915986946881830712137 149495936990210161373034103)
      ·
        refine ⟨224243905485315242059551155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149495936990210161373034103 224243905485315242059551155)
        ·
          refine ⟨336365858227972863089326733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224243905485315242059551155 336365858227972863089326733)
          ·
            refine ⟨126137196835489823658497525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336365858227972863089326733 126137196835489823658497525)
            ·
              refine ⟨11825362203327170967984143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126137196835489823658497525 11825362203327170967984143)
              ·
                refine ⟨17738043304990756451976215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11825362203327170967984143 17738043304990756451976215)
                ·
                  refine ⟨26607064957486134677964323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17738043304990756451976215 26607064957486134677964323)
                  ·
                    refine ⟨39910597436229202016946485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26607064957486134677964323 39910597436229202016946485)
                    ·
                      refine ⟨3741618509646487689088733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39910597436229202016946485 3741618509646487689088733)
                      ·
                        rfl

theorem cell23_7286776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_7286776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286776 prefixEnd_7286776 := by exact prefixLift 7286776
  have htrace : WordTrace (prefixWord ++ tailWord_7286776) baseStart_7286776 baseEnd_7286776 := by
    simpa [prefixWord, tailWord_7286776, baseEnd_7286776] using wordTrace_append hprefix tailTrace_7286776
  have hstable : (prefixWord ++ tailWord_7286776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286776).length < 2 ^ (prefixWord ++ tailWord_7286776).sum := by decide
  have hdescent : baseEnd_7286776 < baseStart_7286776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286807 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7286807 : Nat := 118140960795 + 7286807 * 2 ^ 59
def prefixEnd_7286807 : Nat := 4983230072969 + 3 ^ 40 * 7286807 * 2
def baseEnd_7286807 : Nat := 3741634427546777067801091

theorem tailTrace_7286807 : CollatzResearch.WordTrace tailWord_7286807 prefixEnd_7286807 3741634427546777067801091 := by
  unfold tailWord_7286807
  simp only [CollatzResearch.WordTrace]
  refine ⟨265771685312150201401994675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177181123541433467601329783 265771685312150201401994675)
  ·
    refine ⟨398657527968225302102992013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265771685312150201401994675 398657527968225302102992013)
    ·
      refine ⟨149496572988084488288622005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398657527968225302102992013 149496572988084488288622005)
      ·
        refine ⟨14015303717632920777058313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149496572988084488288622005 14015303717632920777058313)
        ·
          refine ⟨10511477788224690582793735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14015303717632920777058313 10511477788224690582793735)
          ·
            refine ⟨15767216682337035874190603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511477788224690582793735 15767216682337035874190603)
            ·
              refine ⟨23650825023505553811285905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767216682337035874190603 23650825023505553811285905)
              ·
                refine ⟨17738118767629165358464429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23650825023505553811285905 17738118767629165358464429)
                ·
                  refine ⟨6651794537860937009424161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17738118767629165358464429 6651794537860937009424161)
                  ·
                    refine ⟨4988845903395702757068121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651794537860937009424161 4988845903395702757068121)
                    ·
                      refine ⟨3741634427546777067801091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988845903395702757068121 3741634427546777067801091)
                      ·
                        rfl

theorem cell23_7286807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7286807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286807 prefixEnd_7286807 := by exact prefixLift 7286807
  have htrace : WordTrace (prefixWord ++ tailWord_7286807) baseStart_7286807 baseEnd_7286807 := by
    simpa [prefixWord, tailWord_7286807, baseEnd_7286807] using wordTrace_append hprefix tailTrace_7286807
  have hstable : (prefixWord ++ tailWord_7286807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286807).length < 2 ^ (prefixWord ++ tailWord_7286807).sum := by decide
  have hdescent : baseEnd_7286807 < baseStart_7286807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286809 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_7286809 : Nat := 118140960795 + 7286809 * 2 ^ 59
def prefixEnd_7286809 : Nat := 4983230072969 + 3 ^ 40 * 7286809 * 2
def baseEnd_7286809 : Nat := 1247211818169362019992027

theorem tailTrace_7286809 : CollatzResearch.WordTrace tailWord_7286809 prefixEnd_7286809 1247211818169362019992027 := by
  unfold tailWord_7286809
  simp only [CollatzResearch.WordTrace]
  refine ⟨265771758258142955743567481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177181172172095303829044987 265771758258142955743567481)
  ·
    refine ⟨199328818693607216807675611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265771758258142955743567481 199328818693607216807675611)
    ·
      refine ⟨298993228040410825211513417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199328818693607216807675611 298993228040410825211513417)
      ·
        refine ⟨224244921030308118908635063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298993228040410825211513417 224244921030308118908635063)
        ·
          refine ⟨336367381545462178362952595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224244921030308118908635063 336367381545462178362952595)
          ·
            refine ⟨504551072318193267544428893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336367381545462178362952595 504551072318193267544428893)
            ·
              refine ⟨189206652119322475329160835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504551072318193267544428893 189206652119322475329160835)
              ·
                refine ⟨283809978178983712993741253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189206652119322475329160835 283809978178983712993741253)
                ·
                  refine ⟨53214370908559446186326485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283809978178983712993741253 53214370908559446186326485)
                  ·
                    refine ⟨1247211818169362019992027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53214370908559446186326485 1247211818169362019992027)
                    ·
                      rfl

theorem cell23_7286809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_7286809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286809 prefixEnd_7286809 := by exact prefixLift 7286809
  have htrace : WordTrace (prefixWord ++ tailWord_7286809) baseStart_7286809 baseEnd_7286809 := by
    simpa [prefixWord, tailWord_7286809, baseEnd_7286809] using wordTrace_append hprefix tailTrace_7286809
  have hstable : (prefixWord ++ tailWord_7286809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286809).length < 2 ^ (prefixWord ++ tailWord_7286809).sum := by decide
  have hdescent : baseEnd_7286809 < baseStart_7286809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286813 : List Nat := [1, 4, 2, 2, 2, 2, 3, 7]
def baseStart_7286813 : Nat := 118140960795 + 7286813 * 2 ^ 59
def prefixEnd_7286813 : Nat := 4983230072969 + 3 ^ 40 * 7286813 * 2
def baseEnd_7286813 : Nat := 138579166978914964604669

theorem tailTrace_7286813 : CollatzResearch.WordTrace tailWord_7286813 prefixEnd_7286813 138579166978914964604669 := by
  unfold tailWord_7286813
  simp only [CollatzResearch.WordTrace]
  refine ⟨265771904150128464426713093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177181269433418976284475395 265771904150128464426713093)
  ·
    refine ⟨49832232028149087080008705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265771904150128464426713093 49832232028149087080008705)
    ·
      refine ⟨37374174021111815310006529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49832232028149087080008705 37374174021111815310006529)
      ·
        refine ⟨28030630515833861482504897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37374174021111815310006529 28030630515833861482504897)
        ·
          refine ⟨21022972886875396111878673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28030630515833861482504897 21022972886875396111878673)
          ·
            refine ⟨15767229665156547083909005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21022972886875396111878673 15767229665156547083909005)
            ·
              refine ⟨5912711124433705156465877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15767229665156547083909005 5912711124433705156465877)
              ·
                refine ⟨138579166978914964604669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5912711124433705156465877 138579166978914964604669)
                ·
                  rfl

theorem cell23_7286813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 7].length) (baseStart_7286813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286813 prefixEnd_7286813 := by exact prefixLift 7286813
  have htrace : WordTrace (prefixWord ++ tailWord_7286813) baseStart_7286813 baseEnd_7286813 := by
    simpa [prefixWord, tailWord_7286813, baseEnd_7286813] using wordTrace_append hprefix tailTrace_7286813
  have hstable : (prefixWord ++ tailWord_7286813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286813).length < 2 ^ (prefixWord ++ tailWord_7286813).sum := by decide
  have hdescent : baseEnd_7286813 < baseStart_7286813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286824 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7286824 : Nat := 118140960795 + 7286824 * 2 ^ 59
def prefixEnd_7286824 : Nat := 4983230072969 + 3 ^ 40 * 7286824 * 2
def baseEnd_7286824 : Nat := 3741643156717903501288513

theorem tailTrace_7286824 : CollatzResearch.WordTrace tailWord_7286824 prefixEnd_7286824 3741643156717903501288513 := by
  unfold tailWord_7286824
  simp only [CollatzResearch.WordTrace]
  refine ⟨132886152676544306652681763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177181536902059075536909017 132886152676544306652681763)
  ·
    refine ⟨199329229014816459979022645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132886152676544306652681763 199329229014816459979022645)
    ·
      refine ⟨18687115220139043123033373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199329229014816459979022645 18687115220139043123033373)
      ·
        refine ⟨7007668207552141171137515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18687115220139043123033373 7007668207552141171137515)
        ·
          refine ⟨10511502311328211756706273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7007668207552141171137515 10511502311328211756706273)
          ·
            refine ⟨7883626733496158817529705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10511502311328211756706273 7883626733496158817529705)
            ·
              refine ⟨5912720050122119113147279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7883626733496158817529705 5912720050122119113147279)
              ·
                refine ⟨8869080075183178669720919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912720050122119113147279 8869080075183178669720919)
                ·
                  refine ⟨13303620112774768004581379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869080075183178669720919 13303620112774768004581379)
                  ·
                    refine ⟨19955430169162152006872069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13303620112774768004581379 19955430169162152006872069)
                    ·
                      refine ⟨3741643156717903501288513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19955430169162152006872069 3741643156717903501288513)
                      ·
                        rfl

theorem cell23_7286824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7286824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286824 prefixEnd_7286824 := by exact prefixLift 7286824
  have htrace : WordTrace (prefixWord ++ tailWord_7286824) baseStart_7286824 baseEnd_7286824 := by
    simpa [prefixWord, tailWord_7286824, baseEnd_7286824] using wordTrace_append hprefix tailTrace_7286824
  have hstable : (prefixWord ++ tailWord_7286824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286824).length < 2 ^ (prefixWord ++ tailWord_7286824).sum := by decide
  have hdescent : baseEnd_7286824 < baseStart_7286824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286840 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_7286840 : Nat := 118140960795 + 7286840 * 2 ^ 59
def prefixEnd_7286840 : Nat := 4983230072969 + 3 ^ 40 * 7286840 * 2
def baseEnd_7286840 : Nat := 3741651372408375438688439

theorem tailTrace_7286840 : CollatzResearch.WordTrace tailWord_7286840 prefixEnd_7286840 3741651372408375438688439 := by
  unfold tailWord_7286840
  simp only [CollatzResearch.WordTrace]
  refine ⟨132886444460515324018972987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177181925947353765358630649 132886444460515324018972987)
  ·
    refine ⟨199329666690772986028459481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132886444460515324018972987 199329666690772986028459481)
    ·
      refine ⟨149497250018079739521344611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199329666690772986028459481 149497250018079739521344611)
      ·
        refine ⟨224245875027119609282016917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149497250018079739521344611 224245875027119609282016917)
        ·
          refine ⟨10511525391896231685094543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 224245875027119609282016917 10511525391896231685094543)
          ·
            refine ⟨15767288087844347527641815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511525391896231685094543 15767288087844347527641815)
            ·
              refine ⟨23650932131766521291462723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767288087844347527641815 23650932131766521291462723)
              ·
                refine ⟨35476398197649781937194085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23650932131766521291462723 35476398197649781937194085)
                ·
                  refine ⟨6651824662059334113223891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35476398197649781937194085 6651824662059334113223891)
                  ·
                    refine ⟨9977736993089001169835837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6651824662059334113223891 9977736993089001169835837)
                    ·
                      refine ⟨3741651372408375438688439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9977736993089001169835837 3741651372408375438688439)
                      ·
                        rfl

theorem cell23_7286840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_7286840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286840 prefixEnd_7286840 := by exact prefixLift 7286840
  have htrace : WordTrace (prefixWord ++ tailWord_7286840) baseStart_7286840 baseEnd_7286840 := by
    simpa [prefixWord, tailWord_7286840, baseEnd_7286840] using wordTrace_append hprefix tailTrace_7286840
  have hstable : (prefixWord ++ tailWord_7286840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286840).length < 2 ^ (prefixWord ++ tailWord_7286840).sum := by decide
  have hdescent : baseEnd_7286840 < baseStart_7286840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286870 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7286870 : Nat := 118140960795 + 7286870 * 2 ^ 59
def prefixEnd_7286870 : Nat := 4983230072969 + 3 ^ 40 * 7286870 * 2
def baseEnd_7286870 : Nat := 3741666776828010321313301

theorem tailTrace_7286870 : CollatzResearch.WordTrace tailWord_7286870 prefixEnd_7286870 3741666776828010321313301 := by
  unfold tailWord_7286870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610873944432622697596129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177182655407281308774358709 16610873944432622697596129)
  ·
    refine ⟨12458155458324467023197097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16610873944432622697596129 12458155458324467023197097)
    ·
      refine ⟨9343616593743350267397823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12458155458324467023197097 9343616593743350267397823)
      ·
        refine ⟨14015424890615025401096735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9343616593743350267397823 14015424890615025401096735)
        ·
          refine ⟨21023137335922538101645103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14015424890615025401096735 21023137335922538101645103)
          ·
            refine ⟨31534706003883807152467655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023137335922538101645103 31534706003883807152467655)
            ·
              refine ⟨47302059005825710728701483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31534706003883807152467655 47302059005825710728701483)
              ·
                refine ⟨70953088508738566093052225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47302059005825710728701483 70953088508738566093052225)
                ·
                  refine ⟨53214816381553924569789169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70953088508738566093052225 53214816381553924569789169)
                  ·
                    refine ⟨39911112286165443427341877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53214816381553924569789169 39911112286165443427341877)
                    ·
                      refine ⟨3741666776828010321313301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39911112286165443427341877 3741666776828010321313301)
                      ·
                        rfl

theorem cell23_7286870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7286870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286870 prefixEnd_7286870 := by exact prefixLift 7286870
  have htrace : WordTrace (prefixWord ++ tailWord_7286870) baseStart_7286870 baseEnd_7286870 := by
    simpa [prefixWord, tailWord_7286870, baseEnd_7286870] using wordTrace_append hprefix tailTrace_7286870
  have hstable : (prefixWord ++ tailWord_7286870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286870).length < 2 ^ (prefixWord ++ tailWord_7286870).sum := by decide
  have hdescent : baseEnd_7286870 < baseStart_7286870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286880 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 4, 2, 2]
def baseStart_7286880 : Nat := 118140960795 + 7286880 * 2 ^ 59
def prefixEnd_7286880 : Nat := 4983230072969 + 3 ^ 40 * 7286880 * 2
def baseEnd_7286880 : Nat := 3741671911634555282188255

theorem tailTrace_7286880 : CollatzResearch.WordTrace tailWord_7286880 prefixEnd_7286880 3741671911634555282188255 := by
  unfold tailWord_7286880
  simp only [CollatzResearch.WordTrace]
  refine ⟨132887173920442867434701047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177182898560590489912934729 132887173920442867434701047)
  ·
    refine ⟨199330760880664301152051571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132887173920442867434701047 199330760880664301152051571)
    ·
      refine ⟨298996141320996451728077357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199330760880664301152051571 298996141320996451728077357)
      ·
        refine ⟨112123552995373669398029009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298996141320996451728077357 112123552995373669398029009)
        ·
          refine ⟨84092664746530252048521757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112123552995373669398029009 84092664746530252048521757)
          ·
            refine ⟨31534749279948844518195659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84092664746530252048521757 31534749279948844518195659)
            ·
              refine ⟨47302123919923266777293489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31534749279948844518195659 47302123919923266777293489)
              ·
                refine ⟨35476592939942450082970117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47302123919923266777293489 35476592939942450082970117)
                ·
                  refine ⟨6651861176239209390556897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35476592939942450082970117 6651861176239209390556897)
                  ·
                    refine ⟨4988895882179407042917673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651861176239209390556897 4988895882179407042917673)
                    ·
                      refine ⟨3741671911634555282188255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4988895882179407042917673 3741671911634555282188255)
                      ·
                        rfl

theorem cell23_7286880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_7286880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286880 prefixEnd_7286880 := by exact prefixLift 7286880
  have htrace : WordTrace (prefixWord ++ tailWord_7286880) baseStart_7286880 baseEnd_7286880 := by
    simpa [prefixWord, tailWord_7286880, baseEnd_7286880] using wordTrace_append hprefix tailTrace_7286880
  have hstable : (prefixWord ++ tailWord_7286880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286880).length < 2 ^ (prefixWord ++ tailWord_7286880).sum := by decide
  have hdescent : baseEnd_7286880 < baseStart_7286880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286903 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 7]
def baseStart_7286903 : Nat := 118140960795 + 7286903 * 2 ^ 59
def prefixEnd_7286903 : Nat := 4983230072969 + 3 ^ 40 * 7286903 * 2
def baseEnd_7286903 : Nat := 415742635743289854688961

theorem tailTrace_7286903 : CollatzResearch.WordTrace tailWord_7286903 prefixEnd_7286903 415742635743289854688961 := by
  unfold tailWord_7286903
  simp only [CollatzResearch.WordTrace]
  refine ⟨265775186719802409797489363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177183457813201606531659575 265775186719802409797489363)
  ·
    refine ⟨398662780079703614696234045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265775186719802409797489363 398662780079703614696234045)
    ·
      refine ⟨149498542529888855511087767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398662780079703614696234045 149498542529888855511087767)
      ·
        refine ⟨224247813794833283266631651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149498542529888855511087767 224247813794833283266631651)
        ·
          refine ⟨336371720692249924899947477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224247813794833283266631651 336371720692249924899947477)
          ·
            refine ⟨7883712203724607614842519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 336371720692249924899947477 7883712203724607614842519)
            ·
              refine ⟨11825568305586911422263779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7883712203724607614842519 11825568305586911422263779)
              ·
                refine ⟨17738352458380367133395669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11825568305586911422263779 17738352458380367133395669)
                ·
                  refine ⟨415742635743289854688961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17738352458380367133395669 415742635743289854688961)
                  ·
                    rfl

theorem cell23_7286903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 7].length) (baseStart_7286903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286903 prefixEnd_7286903 := by exact prefixLift 7286903
  have htrace : WordTrace (prefixWord ++ tailWord_7286903) baseStart_7286903 baseEnd_7286903 := by
    simpa [prefixWord, tailWord_7286903, baseEnd_7286903] using wordTrace_append hprefix tailTrace_7286903
  have hstable : (prefixWord ++ tailWord_7286903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286903).length < 2 ^ (prefixWord ++ tailWord_7286903).sum := by decide
  have hdescent : baseEnd_7286903 < baseStart_7286903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286933 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_7286933 : Nat := 118140960795 + 7286933 * 2 ^ 59
def prefixEnd_7286933 : Nat := 4983230072969 + 3 ^ 40 * 7286933 * 2
def baseEnd_7286933 : Nat := 1247233042036414524941837

theorem tailTrace_7286933 : CollatzResearch.WordTrace tailWord_7286933 prefixEnd_7286933 1247233042036414524941837 := by
  unfold tailWord_7286933
  simp only [CollatzResearch.WordTrace]
  refine ⟨265776280909693724921081453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177184187273129149947387635 265776280909693724921081453)
  ·
    refine ⟨99666105341135146845405545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265776280909693724921081453 99666105341135146845405545)
    ·
      refine ⟨74749579005851360134054159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99666105341135146845405545 74749579005851360134054159)
      ·
        refine ⟨112124368508777040201081239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74749579005851360134054159 112124368508777040201081239)
        ·
          refine ⟨168186552763165560301621859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112124368508777040201081239 168186552763165560301621859)
          ·
            refine ⟨252279829144748340452432789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168186552763165560301621859 252279829144748340452432789)
            ·
              refine ⟨11825616991160078458707787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252279829144748340452432789 11825616991160078458707787)
              ·
                refine ⟨17738425486740117688061681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11825616991160078458707787 17738425486740117688061681)
                ·
                  refine ⟨13303819115055088266046261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17738425486740117688061681 13303819115055088266046261)
                  ·
                    refine ⟨1247233042036414524941837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13303819115055088266046261 1247233042036414524941837)
                    ·
                      rfl

theorem cell23_7286933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_7286933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286933 prefixEnd_7286933 := by exact prefixLift 7286933
  have htrace : WordTrace (prefixWord ++ tailWord_7286933) baseStart_7286933 baseEnd_7286933 := by
    simpa [prefixWord, tailWord_7286933, baseEnd_7286933] using wordTrace_append hprefix tailTrace_7286933
  have hstable : (prefixWord ++ tailWord_7286933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286933).length < 2 ^ (prefixWord ++ tailWord_7286933).sum := by decide
  have hdescent : baseEnd_7286933 < baseStart_7286933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286943 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7286943 : Nat := 118140960795 + 7286943 * 2 ^ 59
def prefixEnd_7286943 : Nat := 4983230072969 + 3 ^ 40 * 7286943 * 2
def baseEnd_7286943 : Nat := 3741704260915788535700465

theorem tailTrace_7286943 : CollatzResearch.WordTrace tailWord_7286943 prefixEnd_7286943 3741704260915788535700465 := by
  unfold tailWord_7286943
  simp only [CollatzResearch.WordTrace]
  refine ⟨265776645639657496628945483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177184430426438331085963655 265776645639657496628945483)
  ·
    refine ⟨398664968459486244943418225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265776645639657496628945483 398664968459486244943418225)
    ·
      refine ⟨298998726344614683707563669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398664968459486244943418225 298998726344614683707563669)
      ·
        refine ⟨14015565297403813298792047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 298998726344614683707563669 14015565297403813298792047)
        ·
          refine ⟨21023347946105719948188071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14015565297403813298792047 21023347946105719948188071)
          ·
            refine ⟨31535021919158579922282107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023347946105719948188071 31535021919158579922282107)
            ·
              refine ⟨47302532878737869883423161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31535021919158579922282107 47302532878737869883423161)
              ·
                refine ⟨35476899659053402412567371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47302532878737869883423161 35476899659053402412567371)
                ·
                  refine ⟨53215349488580103618851057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35476899659053402412567371 53215349488580103618851057)
                  ·
                    refine ⟨39911512116435077714138293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53215349488580103618851057 39911512116435077714138293)
                    ·
                      refine ⟨3741704260915788535700465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39911512116435077714138293 3741704260915788535700465)
                      ·
                        rfl

theorem cell23_7286943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7286943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286943 prefixEnd_7286943 := by exact prefixLift 7286943
  have htrace : WordTrace (prefixWord ++ tailWord_7286943) baseStart_7286943 baseEnd_7286943 := by
    simpa [prefixWord, tailWord_7286943, baseEnd_7286943] using wordTrace_append hprefix tailTrace_7286943
  have hstable : (prefixWord ++ tailWord_7286943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286943).length < 2 ^ (prefixWord ++ tailWord_7286943).sum := by decide
  have hdescent : baseEnd_7286943 < baseStart_7286943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286963 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 3, 4]
def baseStart_7286963 : Nat := 118140960795 + 7286963 * 2 ^ 59
def prefixEnd_7286963 : Nat := 4983230072969 + 3 ^ 40 * 7286963 * 2
def baseEnd_7286963 : Nat := 1247238176842959485816791

theorem tailTrace_7286963 : CollatzResearch.WordTrace tailWord_7286963 prefixEnd_7286963 1247238176842959485816791 := by
  unfold tailWord_7286963
  simp only [CollatzResearch.WordTrace]
  refine ⟨265777375099585040044673543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177184916733056693363115695 265777375099585040044673543)
  ·
    refine ⟨398666062649377560067010315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265777375099585040044673543 398666062649377560067010315)
    ·
      refine ⟨597999093974066340100515473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398666062649377560067010315 597999093974066340100515473)
      ·
        refine ⟨448499320480549755075386605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597999093974066340100515473 448499320480549755075386605)
        ·
          refine ⟨168187245180206158153269977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448499320480549755075386605 168187245180206158153269977)
          ·
            refine ⟨126140433885154618614952483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168187245180206158153269977 126140433885154618614952483)
            ·
              refine ⟨189210650827731927922428725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126140433885154618614952483 189210650827731927922428725)
              ·
                refine ⟨17738498515099868242727693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189210650827731927922428725 17738498515099868242727693)
                ·
                  refine ⟨6651936943162450591022885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17738498515099868242727693 6651936943162450591022885)
                  ·
                    refine ⟨1247238176842959485816791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6651936943162450591022885 1247238176842959485816791)
                    ·
                      rfl

theorem cell23_7286963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 4].length) (baseStart_7286963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286963 prefixEnd_7286963 := by exact prefixLift 7286963
  have htrace : WordTrace (prefixWord ++ tailWord_7286963) baseStart_7286963 baseEnd_7286963 := by
    simpa [prefixWord, tailWord_7286963, baseEnd_7286963] using wordTrace_append hprefix tailTrace_7286963
  have hstable : (prefixWord ++ tailWord_7286963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286963).length < 2 ^ (prefixWord ++ tailWord_7286963).sum := by decide
  have hdescent : baseEnd_7286963 < baseStart_7286963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286973 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_7286973 : Nat := 118140960795 + 7286973 * 2 ^ 59
def prefixEnd_7286973 : Nat := 4983230072969 + 3 ^ 40 * 7286973 * 2
def baseEnd_7286973 : Nat := 3741719665335423418325327

theorem tailTrace_7286973 : CollatzResearch.WordTrace tailWord_7286973 prefixEnd_7286973 3741719665335423418325327 := by
  unfold tailWord_7286973
  simp only [CollatzResearch.WordTrace]
  refine ⟨265777739829548811752537573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177185159886365874501691715 265777739829548811752537573)
  ·
    refine ⟨49833326218040402203600795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265777739829548811752537573 49833326218040402203600795)
    ·
      refine ⟨74749989327060603305401193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49833326218040402203600795 74749989327060603305401193)
      ·
        refine ⟨56062491995295452479050895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74749989327060603305401193 56062491995295452479050895)
        ·
          refine ⟨84093737992943178718576343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56062491995295452479050895 84093737992943178718576343)
          ·
            refine ⟨126140606989414768077864515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84093737992943178718576343 126140606989414768077864515)
            ·
              refine ⟨189210910484122152116796773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126140606989414768077864515 189210910484122152116796773)
              ·
                refine ⟨35477045715772903521899395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189210910484122152116796773 35477045715772903521899395)
                ·
                  refine ⟨53215568573659355282849093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35477045715772903521899395 53215568573659355282849093)
                  ·
                    refine ⟨9977919107561129115534205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53215568573659355282849093 9977919107561129115534205)
                    ·
                      refine ⟨3741719665335423418325327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9977919107561129115534205 3741719665335423418325327)
                      ·
                        rfl

theorem cell23_7286973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_7286973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286973 prefixEnd_7286973 := by exact prefixLift 7286973
  have htrace : WordTrace (prefixWord ++ tailWord_7286973) baseStart_7286973 baseEnd_7286973 := by
    simpa [prefixWord, tailWord_7286973, baseEnd_7286973] using wordTrace_append hprefix tailTrace_7286973
  have hstable : (prefixWord ++ tailWord_7286973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286973).length < 2 ^ (prefixWord ++ tailWord_7286973).sum := by decide
  have hdescent : baseEnd_7286973 < baseStart_7286973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286980 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_7286980 : Nat := 118140960795 + 7286980 * 2 ^ 59
def prefixEnd_7286980 : Nat := 4983230072969 + 3 ^ 40 * 7286980 * 2
def baseEnd_7286980 : Nat := 1247241086566668296979265

theorem tailTrace_7286980 : CollatzResearch.WordTrace tailWord_7286980 prefixEnd_7286980 1247241086566668296979265 := by
  unfold tailWord_7286980
  simp only [CollatzResearch.WordTrace]
  refine ⟨132888997570261725974021197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177185330093682301298694929 132888997570261725974021197)
  ·
    refine ⟨49833374088848147240257949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132888997570261725974021197 49833374088848147240257949)
    ·
      refine ⟨18687515283318055215096731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49833374088848147240257949 18687515283318055215096731)
      ·
        refine ⟨28031272924977082822645097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18687515283318055215096731 28031272924977082822645097)
        ·
          refine ⟨21023454693732812116983823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28031272924977082822645097 21023454693732812116983823)
          ·
            refine ⟨31535182040599218175475735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023454693732812116983823 31535182040599218175475735)
            ·
              refine ⟨47302773060898827263213603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31535182040599218175475735 47302773060898827263213603)
              ·
                refine ⟨70954159591348240894820405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47302773060898827263213603 70954159591348240894820405)
                ·
                  refine ⟨6651952461688897583889413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70954159591348240894820405 6651952461688897583889413)
                  ·
                    refine ⟨1247241086566668296979265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6651952461688897583889413 1247241086566668296979265)
                    ·
                      rfl

theorem cell23_7286980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_7286980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286980 prefixEnd_7286980 := by exact prefixLift 7286980
  have htrace : WordTrace (prefixWord ++ tailWord_7286980) baseStart_7286980 baseEnd_7286980 := by
    simpa [prefixWord, tailWord_7286980, baseEnd_7286980] using wordTrace_append hprefix tailTrace_7286980
  have hstable : (prefixWord ++ tailWord_7286980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286980).length < 2 ^ (prefixWord ++ tailWord_7286980).sum := by decide
  have hdescent : baseEnd_7286980 < baseStart_7286980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7286990 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_7286990 : Nat := 118140960795 + 7286990 * 2 ^ 59
def prefixEnd_7286990 : Nat := 4983230072969 + 3 ^ 40 * 7286990 * 2
def baseEnd_7286990 : Nat := 3741728394506549851812749

theorem tailTrace_7286990 : CollatzResearch.WordTrace tailWord_7286990 prefixEnd_7286990 3741728394506549851812749 := by
  unfold tailWord_7286990
  simp only [CollatzResearch.WordTrace]
  refine ⟨33222294983810902956988303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177185573246991482437270949 33222294983810902956988303)
  ·
    refine ⟨49833442475716354435482455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33222294983810902956988303 49833442475716354435482455)
    ·
      refine ⟨74750163713574531653223683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49833442475716354435482455 74750163713574531653223683)
      ·
        refine ⟨112125245570361797479835525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74750163713574531653223683 112125245570361797479835525)
        ·
          refine ⟨21023483544442837027469161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112125245570361797479835525 21023483544442837027469161)
          ·
            refine ⟨15767612658332127770601871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21023483544442837027469161 15767612658332127770601871)
            ·
              refine ⟨23651418987498191655902807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767612658332127770601871 23651418987498191655902807)
              ·
                refine ⟨35477128481247287483854211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23651418987498191655902807 35477128481247287483854211)
                ·
                  refine ⟨53215692721870931225781317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35477128481247287483854211 53215692721870931225781317)
                  ·
                    refine ⟨9977942385350799604833997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53215692721870931225781317 9977942385350799604833997)
                    ·
                      refine ⟨3741728394506549851812749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9977942385350799604833997 3741728394506549851812749)
                      ·
                        rfl

theorem cell23_7286990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_7286990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7286990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7286990 prefixEnd_7286990 := by exact prefixLift 7286990
  have htrace : WordTrace (prefixWord ++ tailWord_7286990) baseStart_7286990 baseEnd_7286990 := by
    simpa [prefixWord, tailWord_7286990, baseEnd_7286990] using wordTrace_append hprefix tailTrace_7286990
  have hstable : (prefixWord ++ tailWord_7286990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7286990).length < 2 ^ (prefixWord ++ tailWord_7286990).sum := by decide
  have hdescent : baseEnd_7286990 < baseStart_7286990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7286990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287013 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7287013 : Nat := 118140960795 + 7287013 * 2 ^ 59
def prefixEnd_7287013 : Nat := 4983230072969 + 3 ^ 40 * 7287013 * 2
def baseEnd_7287013 : Nat := 3741740204561603261825143

theorem tailTrace_7287013 : CollatzResearch.WordTrace tailWord_7287013 prefixEnd_7287013 3741740204561603261825143 := by
  unfold tailWord_7287013
  simp only [CollatzResearch.WordTrace]
  refine ⟨265779198749403898583993693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177186132499602599055995795 265779198749403898583993693)
  ·
    refine ⟨99667199531026461968997635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265779198749403898583993693 99667199531026461968997635)
    ·
      refine ⟨149500799296539692953496453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99667199531026461968997635 149500799296539692953496453)
      ·
        refine ⟨28031399868101192428780585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149500799296539692953496453 28031399868101192428780585)
        ·
          refine ⟨21023549901075894321585439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28031399868101192428780585 21023549901075894321585439)
          ·
            refine ⟨31535324851613841482378159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023549901075894321585439 31535324851613841482378159)
            ·
              refine ⟨47302987277420762223567239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31535324851613841482378159 47302987277420762223567239)
              ·
                refine ⟨70954480916131143335350859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47302987277420762223567239 70954480916131143335350859)
                ·
                  refine ⟨106431721374196715003026289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70954480916131143335350859 106431721374196715003026289)
                  ·
                    refine ⟨79823791030647536252269717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106431721374196715003026289 79823791030647536252269717)
                    ·
                      refine ⟨3741740204561603261825143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79823791030647536252269717 3741740204561603261825143)
                      ·
                        rfl

theorem cell23_7287013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7287013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287013 prefixEnd_7287013 := by exact prefixLift 7287013
  have htrace : WordTrace (prefixWord ++ tailWord_7287013) baseStart_7287013 baseEnd_7287013 := by
    simpa [prefixWord, tailWord_7287013, baseEnd_7287013] using wordTrace_append hprefix tailTrace_7287013
  have hstable : (prefixWord ++ tailWord_7287013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287013).length < 2 ^ (prefixWord ++ tailWord_7287013).sum := by decide
  have hdescent : baseEnd_7287013 < baseStart_7287013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287071 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 1, 1, 3]
def baseStart_7287071 : Nat := 118140960795 + 7287071 * 2 ^ 59
def prefixEnd_7287071 : Nat := 4983230072969 + 3 ^ 40 * 7287071 * 2
def baseEnd_7287071 : Nat := 3741769986439564034899877

theorem tailTrace_7287071 : CollatzResearch.WordTrace tailWord_7287071 prefixEnd_7287071 3741769986439564034899877 := by
  unfold tailWord_7287071
  simp only [CollatzResearch.WordTrace]
  refine ⟨265781314183193774489605067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177187542788795849659736711 265781314183193774489605067)
  ·
    refine ⟨398671971274790661734407601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265781314183193774489605067 398671971274790661734407601)
    ·
      refine ⟨299003978456092996300805701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398671971274790661734407601 299003978456092996300805701)
      ·
        refine ⟨56063245960517436806401069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299003978456092996300805701 56063245960517436806401069)
        ·
          refine ⟨21023717235194038802400401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56063245960517436806401069 21023717235194038802400401)
          ·
            refine ⟨15767787926395529101800301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21023717235194038802400401 15767787926395529101800301)
            ·
              refine ⟨5912920472398323413175113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15767787926395529101800301 5912920472398323413175113)
              ·
                refine ⟨4434690354298742559881335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912920472398323413175113 4434690354298742559881335)
                ·
                  refine ⟨6652035531448113839822003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434690354298742559881335 6652035531448113839822003)
                  ·
                    refine ⟨9978053297172170759733005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652035531448113839822003 9978053297172170759733005)
                    ·
                      refine ⟨3741769986439564034899877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978053297172170759733005 3741769986439564034899877)
                      ·
                        rfl

theorem cell23_7287071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_7287071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287071 prefixEnd_7287071 := by exact prefixLift 7287071
  have htrace : WordTrace (prefixWord ++ tailWord_7287071) baseStart_7287071 baseEnd_7287071 := by
    simpa [prefixWord, tailWord_7287071, baseEnd_7287071] using wordTrace_append hprefix tailTrace_7287071
  have hstable : (prefixWord ++ tailWord_7287071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287071).length < 2 ^ (prefixWord ++ tailWord_7287071).sum := by decide
  have hdescent : baseEnd_7287071 < baseStart_7287071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287073 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7287073 : Nat := 118140960795 + 7287073 * 2 ^ 59
def prefixEnd_7287073 : Nat := 4983230072969 + 3 ^ 40 * 7287073 * 2
def baseEnd_7287073 : Nat := 3741771013400873027074867

theorem tailTrace_7287073 : CollatzResearch.WordTrace tailWord_7287073 prefixEnd_7287073 3741771013400873027074867 := by
  unfold tailWord_7287073
  simp only [CollatzResearch.WordTrace]
  refine ⟨265781387129186528831177873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177187591419457685887451915 265781387129186528831177873)
  ·
    refine ⟨199336040346889896623383405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265781387129186528831177873 199336040346889896623383405)
    ·
      refine ⟨74751015130083711233768777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199336040346889896623383405 74751015130083711233768777)
      ·
        refine ⟨56063261347562783425326583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74751015130083711233768777 56063261347562783425326583)
        ·
          refine ⟨84094892021344175137989875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56063261347562783425326583 84094892021344175137989875)
          ·
            refine ⟨126142338032016262706984813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84094892021344175137989875 126142338032016262706984813)
            ·
              refine ⟨47303376762006098515119305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126142338032016262706984813 47303376762006098515119305)
              ·
                refine ⟨35477532571504573886339479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47303376762006098515119305 35477532571504573886339479)
                ·
                  refine ⟨53216298857256860829509219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35477532571504573886339479 53216298857256860829509219)
                  ·
                    refine ⟨79824448285885291244263829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53216298857256860829509219 79824448285885291244263829)
                    ·
                      refine ⟨3741771013400873027074867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79824448285885291244263829 3741771013400873027074867)
                      ·
                        rfl

theorem cell23_7287073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7287073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287073 prefixEnd_7287073 := by exact prefixLift 7287073
  have htrace : WordTrace (prefixWord ++ tailWord_7287073) baseStart_7287073 baseEnd_7287073 := by
    simpa [prefixWord, tailWord_7287073, baseEnd_7287073] using wordTrace_append hprefix tailTrace_7287073
  have hstable : (prefixWord ++ tailWord_7287073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287073).length < 2 ^ (prefixWord ++ tailWord_7287073).sum := by decide
  have hdescent : baseEnd_7287073 < baseStart_7287073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287087 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 2, 4]
def baseStart_7287087 : Nat := 118140960795 + 7287087 * 2 ^ 59
def prefixEnd_7287087 : Nat := 4983230072969 + 3 ^ 40 * 7287087 * 2
def baseEnd_7287087 : Nat := 1247259400710011990766601

theorem tailTrace_7287087 : CollatzResearch.WordTrace tailWord_7287087 prefixEnd_7287087 1247259400710011990766601 := by
  unfold tailWord_7287087
  simp only [CollatzResearch.WordTrace]
  refine ⟨265781897751135809222187515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177187931834090539481458343 265781897751135809222187515)
  ·
    refine ⟨398672846626703713833281273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265781897751135809222187515 398672846626703713833281273)
    ·
      refine ⟨299004634970027785374960955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398672846626703713833281273 299004634970027785374960955)
      ·
        refine ⟨448506952455041678062441433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299004634970027785374960955 448506952455041678062441433)
        ·
          refine ⟨336380214341281258546831075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448506952455041678062441433 336380214341281258546831075)
          ·
            refine ⟨504570321511921887820246613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336380214341281258546831075 504570321511921887820246613)
            ·
              refine ⟨5912933455217834622893515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 504570321511921887820246613 5912933455217834622893515)
              ·
                refine ⟨8869400182826751934340273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912933455217834622893515 8869400182826751934340273)
                ·
                  refine ⟨6652050137120063950755205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8869400182826751934340273 6652050137120063950755205)
                  ·
                    refine ⟨1247259400710011990766601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652050137120063950755205 1247259400710011990766601)
                    ·
                      rfl

theorem cell23_7287087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 2, 4].length) (baseStart_7287087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287087 prefixEnd_7287087 := by exact prefixLift 7287087
  have htrace : WordTrace (prefixWord ++ tailWord_7287087) baseStart_7287087 baseEnd_7287087 := by
    simpa [prefixWord, tailWord_7287087, baseEnd_7287087] using wordTrace_append hprefix tailTrace_7287087
  have hstable : (prefixWord ++ tailWord_7287087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287087).length < 2 ^ (prefixWord ++ tailWord_7287087).sum := by decide
  have hdescent : baseEnd_7287087 < baseStart_7287087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287097 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7287097 : Nat := 118140960795 + 7287097 * 2 ^ 59
def prefixEnd_7287097 : Nat := 4983230072969 + 3 ^ 40 * 7287097 * 2
def baseEnd_7287097 : Nat := 3741783336936580933174757

theorem tailTrace_7287097 : CollatzResearch.WordTrace tailWord_7287097 prefixEnd_7287097 3741783336936580933174757 := by
  unfold tailWord_7287097
  simp only [CollatzResearch.WordTrace]
  refine ⟨265782262481099580930051545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177188174987399720620034363 265782262481099580930051545)
  ·
    refine ⟨199336696860824685697538659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265782262481099580930051545 199336696860824685697538659)
    ·
      refine ⟨299005045291237028546307989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199336696860824685697538659 299005045291237028546307989)
      ·
        refine ⟨14015861498026735713108187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 299005045291237028546307989 14015861498026735713108187)
        ·
          refine ⟨21023792247040103569662281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14015861498026735713108187 21023792247040103569662281)
          ·
            refine ⟨15767844185280077677246711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21023792247040103569662281 15767844185280077677246711)
            ·
              refine ⟨23651766277920116515870067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767844185280077677246711 23651766277920116515870067)
              ·
                refine ⟨35477649416880174773805101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23651766277920116515870067 35477649416880174773805101)
                ·
                  refine ⟨13304118531330065540176913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35477649416880174773805101 13304118531330065540176913)
                  ·
                    refine ⟨9978088898497549155132685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13304118531330065540176913 9978088898497549155132685)
                    ·
                      refine ⟨3741783336936580933174757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978088898497549155132685 3741783336936580933174757)
                      ·
                        rfl

theorem cell23_7287097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7287097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287097 prefixEnd_7287097 := by exact prefixLift 7287097
  have htrace : WordTrace (prefixWord ++ tailWord_7287097) baseStart_7287097 baseEnd_7287097 := by
    simpa [prefixWord, tailWord_7287097, baseEnd_7287097] using wordTrace_append hprefix tailTrace_7287097
  have hstable : (prefixWord ++ tailWord_7287097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287097).length < 2 ^ (prefixWord ++ tailWord_7287097).sum := by decide
  have hdescent : baseEnd_7287097 < baseStart_7287097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287144 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_7287144 : Nat := 118140960795 + 7287144 * 2 ^ 59
def prefixEnd_7287144 : Nat := 4983230072969 + 3 ^ 40 * 7287144 * 2
def baseEnd_7287144 : Nat := 3741807470527342249287041

theorem tailTrace_7287144 : CollatzResearch.WordTrace tailWord_7287144 prefixEnd_7287144 3741807470527342249287041 := by
  unfold tailWord_7287144
  simp only [CollatzResearch.WordTrace]
  refine ⟨132891988355964653978506243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177189317807952871971341657 132891988355964653978506243)
  ·
    refine ⟨199337982533946980967759365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132891988355964653978506243 199337982533946980967759365)
    ·
      refine ⟨37375871725115058931454881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199337982533946980967759365 37375871725115058931454881)
      ·
        refine ⟨28031903793836294198591161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37375871725115058931454881 28031903793836294198591161)
        ·
          refine ⟨21023927845377220648943371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28031903793836294198591161 21023927845377220648943371)
          ·
            refine ⟨31535891768065830973415057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023927845377220648943371 31535891768065830973415057)
            ·
              refine ⟨23651918826049373230061293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31535891768065830973415057 23651918826049373230061293)
              ·
                refine ⟨8869469559768514961272985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23651918826049373230061293 8869469559768514961272985)
                ·
                  refine ⟨6652102169826386220954739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8869469559768514961272985 6652102169826386220954739)
                  ·
                    refine ⟨9978153254739579331432109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652102169826386220954739 9978153254739579331432109)
                    ·
                      refine ⟨3741807470527342249287041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978153254739579331432109 3741807470527342249287041)
                      ·
                        rfl

theorem cell23_7287144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_7287144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287144 prefixEnd_7287144 := by exact prefixLift 7287144
  have htrace : WordTrace (prefixWord ++ tailWord_7287144) baseStart_7287144 baseEnd_7287144 := by
    simpa [prefixWord, tailWord_7287144, baseEnd_7287144] using wordTrace_append hprefix tailTrace_7287144
  have hstable : (prefixWord ++ tailWord_7287144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287144).length < 2 ^ (prefixWord ++ tailWord_7287144).sum := by decide
  have hdescent : baseEnd_7287144 < baseStart_7287144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287167 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 6, 2, 2]
def baseStart_7287167 : Nat := 118140960795 + 7287167 * 2 ^ 59
def prefixEnd_7287167 : Nat := 4983230072969 + 3 ^ 40 * 7287167 * 2
def baseEnd_7287167 : Nat := 3741819280582395659299435

theorem tailTrace_7287167 : CollatzResearch.WordTrace tailWord_7287167 prefixEnd_7287167 3741819280582395659299435 := by
  unfold tailWord_7287167
  simp only [CollatzResearch.WordTrace]
  refine ⟨265784815590845982885099755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177189877060563988590066503 265784815590845982885099755)
  ·
    refine ⟨398677223386268974327649633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265784815590845982885099755 398677223386268974327649633)
    ·
      refine ⟨299007917539701730745737225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398677223386268974327649633 299007917539701730745737225)
      ·
        refine ⟨224255938154776298059302919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299007917539701730745737225 224255938154776298059302919)
        ·
          refine ⟨336383907232164447088954379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224255938154776298059302919 336383907232164447088954379)
          ·
            refine ⟨504575860848246670633431569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336383907232164447088954379 504575860848246670633431569)
            ·
              refine ⟨378431895636185002975073677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504575860848246670633431569 378431895636185002975073677)
              ·
                refine ⟨141911960863569376115652629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378431895636185002975073677 141911960863569376115652629)
                ·
                  refine ⟨6652123165479814505421217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141911960863569376115652629 6652123165479814505421217)
                  ·
                    refine ⟨4989092374109860879065913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6652123165479814505421217 4989092374109860879065913)
                    ·
                      refine ⟨3741819280582395659299435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989092374109860879065913 3741819280582395659299435)
                      ·
                        rfl

theorem cell23_7287167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_7287167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287167 prefixEnd_7287167 := by exact prefixLift 7287167
  have htrace : WordTrace (prefixWord ++ tailWord_7287167) baseStart_7287167 baseEnd_7287167 := by
    simpa [prefixWord, tailWord_7287167, baseEnd_7287167] using wordTrace_append hprefix tailTrace_7287167
  have hstable : (prefixWord ++ tailWord_7287167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287167).length < 2 ^ (prefixWord ++ tailWord_7287167).sum := by decide
  have hdescent : baseEnd_7287167 < baseStart_7287167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287173 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 11]
def baseStart_7287173 : Nat := 118140960795 + 7287173 * 2 ^ 59
def prefixEnd_7287173 : Nat := 4983230072969 + 3 ^ 40 * 7287173 * 2
def baseEnd_7287173 : Nat := 415758040162924737313823

theorem tailTrace_7287173 : CollatzResearch.WordTrace tailWord_7287173 prefixEnd_7287173 415758040162924737313823 := by
  unfold tailWord_7287173
  simp only [CollatzResearch.WordTrace]
  refine ⟨265785034428824245909818173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177190022952549497273212115 265785034428824245909818173)
  ·
    refine ⟨99669387910809092216181815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265785034428824245909818173 99669387910809092216181815)
    ·
      refine ⟨149504081866213638324272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99669387910809092216181815 149504081866213638324272723)
      ·
        refine ⟨224256122799320457486409085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149504081866213638324272723 224256122799320457486409085)
        ·
          refine ⟨84096046049745171557403407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224256122799320457486409085 84096046049745171557403407)
          ·
            refine ⟨126144069074617757336105111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84096046049745171557403407 126144069074617757336105111)
            ·
              refine ⟨189216103611926636004157667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126144069074617757336105111 189216103611926636004157667)
              ·
                refine ⟨283824155417889954006236501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189216103611926636004157667 283824155417889954006236501)
                ·
                  refine ⟨415758040162924737313823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 283824155417889954006236501 415758040162924737313823)
                  ·
                    rfl

theorem cell23_7287173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_7287173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287173 prefixEnd_7287173 := by exact prefixLift 7287173
  have htrace : WordTrace (prefixWord ++ tailWord_7287173) baseStart_7287173 baseEnd_7287173 := by
    simpa [prefixWord, tailWord_7287173, baseEnd_7287173] using wordTrace_append hprefix tailTrace_7287173
  have hstable : (prefixWord ++ tailWord_7287173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287173).length < 2 ^ (prefixWord ++ tailWord_7287173).sum := by decide
  have hdescent : baseEnd_7287173 < baseStart_7287173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287178 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7287178 : Nat := 118140960795 + 7287178 * 2 ^ 59
def prefixEnd_7287178 : Nat := 4983230072969 + 3 ^ 40 * 7287178 * 2
def baseEnd_7287178 : Nat := 3741824928869595116261885

theorem tailTrace_7287178 : CollatzResearch.WordTrace tailWord_7287178 prefixEnd_7287178 3741824928869595116261885 := by
  unfold tailWord_7287178
  simp only [CollatzResearch.WordTrace]
  refine ⟨66446304198451532940937547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177190144529204087842500125 66446304198451532940937547)
  ·
    refine ⟨99669456297677299411406321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66446304198451532940937547 99669456297677299411406321)
    ·
      refine ⟨74752092223257974558554741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99669456297677299411406321 74752092223257974558554741)
      ·
        refine ⟨7008008645930435114864507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74752092223257974558554741 7008008645930435114864507)
        ·
          refine ⟨10512012968895652672296761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008008645930435114864507 10512012968895652672296761)
          ·
            refine ⟨7884009726671739504222571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10512012968895652672296761 7884009726671739504222571)
            ·
              refine ⟨11826014590007609256333857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884009726671739504222571 11826014590007609256333857)
              ·
                refine ⟨8869510942505706942250393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11826014590007609256333857 8869510942505706942250393)
                ·
                  refine ⟨6652133206879280206687795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8869510942505706942250393 6652133206879280206687795)
                  ·
                    refine ⟨9978199810318920310031693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652133206879280206687795 9978199810318920310031693)
                    ·
                      refine ⟨3741824928869595116261885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978199810318920310031693 3741824928869595116261885)
                      ·
                        rfl

theorem cell23_7287178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7287178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287178 prefixEnd_7287178 := by exact prefixLift 7287178
  have htrace : WordTrace (prefixWord ++ tailWord_7287178) baseStart_7287178 baseEnd_7287178 := by
    simpa [prefixWord, tailWord_7287178, baseEnd_7287178] using wordTrace_append hprefix tailTrace_7287178
  have hstable : (prefixWord ++ tailWord_7287178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287178).length < 2 ^ (prefixWord ++ tailWord_7287178).sum := by decide
  have hdescent : baseEnd_7287178 < baseStart_7287178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287180 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7287180 : Nat := 118140960795 + 7287180 * 2 ^ 59
def prefixEnd_7287180 : Nat := 4983230072969 + 3 ^ 40 * 7287180 * 2
def baseEnd_7287180 : Nat := 3741825955830904108436875

theorem tailTrace_7287180 : CollatzResearch.WordTrace tailWord_7287180 prefixEnd_7287180 3741825955830904108436875 := by
  unfold tailWord_7287180
  simp only [CollatzResearch.WordTrace]
  refine ⟨132892644869899443052661497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177190193159865924070215329 132892644869899443052661497)
  ·
    refine ⟨99669483652424582289496123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132892644869899443052661497 99669483652424582289496123)
    ·
      refine ⟨149504225478636873434244185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99669483652424582289496123 149504225478636873434244185)
      ·
        refine ⟨112128169108977655075683139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149504225478636873434244185 112128169108977655075683139)
        ·
          refine ⟨168192253663466482613524709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112128169108977655075683139 168192253663466482613524709)
          ·
            refine ⟨31536047561899965490035883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168192253663466482613524709 31536047561899965490035883)
            ·
              refine ⟨47304071342849948235053825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31536047561899965490035883 47304071342849948235053825)
              ·
                refine ⟨35478053507137461176290369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47304071342849948235053825 35478053507137461176290369)
                ·
                  refine ⟨26608540130353095882217777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35478053507137461176290369 26608540130353095882217777)
                  ·
                    refine ⟨19956405097764821911663333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26608540130353095882217777 19956405097764821911663333)
                    ·
                      refine ⟨3741825955830904108436875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19956405097764821911663333 3741825955830904108436875)
                      ·
                        rfl

theorem cell23_7287180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7287180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287180 prefixEnd_7287180 := by exact prefixLift 7287180
  have htrace : WordTrace (prefixWord ++ tailWord_7287180) baseStart_7287180 baseEnd_7287180 := by
    simpa [prefixWord, tailWord_7287180, baseEnd_7287180] using wordTrace_append hprefix tailTrace_7287180
  have hstable : (prefixWord ++ tailWord_7287180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287180).length < 2 ^ (prefixWord ++ tailWord_7287180).sum := by decide
  have hdescent : baseEnd_7287180 < baseStart_7287180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287257 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 6, 2]
def baseStart_7287257 : Nat := 118140960795 + 7287257 * 2 ^ 59
def prefixEnd_7287257 : Nat := 4983230072969 + 3 ^ 40 * 7287257 * 2
def baseEnd_7287257 : Nat := 3741865493841300307174021

theorem tailTrace_7287257 : CollatzResearch.WordTrace tailWord_7287257 prefixEnd_7287257 3741865493841300307174021 := by
  unfold tailWord_7287257
  simp only [CollatzResearch.WordTrace]
  refine ⟨265788098160519928255876025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177192065440346618837250683 265788098160519928255876025)
  ·
    refine ⟨199341073620389946191907019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265788098160519928255876025 199341073620389946191907019)
    ·
      refine ⟨299011610430584919287860529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199341073620389946191907019 299011610430584919287860529)
      ·
        refine ⟨224258707822938689465895397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299011610430584919287860529 224258707822938689465895397)
        ·
          refine ⟨42048507716801004274855387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224258707822938689465895397 42048507716801004274855387)
          ·
            refine ⟨63072761575201506412283081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42048507716801004274855387 63072761575201506412283081)
            ·
              refine ⟨47304571181401129809212311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63072761575201506412283081 47304571181401129809212311)
              ·
                refine ⟨70956856772101694713818467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47304571181401129809212311 70956856772101694713818467)
                ·
                  refine ⟨106435285158152542070727701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70956856772101694713818467 106435285158152542070727701)
                  ·
                    refine ⟨4989153991788400409565361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106435285158152542070727701 4989153991788400409565361)
                    ·
                      refine ⟨3741865493841300307174021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989153991788400409565361 3741865493841300307174021)
                      ·
                        rfl

theorem cell23_7287257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_7287257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287257 prefixEnd_7287257 := by exact prefixLift 7287257
  have htrace : WordTrace (prefixWord ++ tailWord_7287257) baseStart_7287257 baseEnd_7287257 := by
    simpa [prefixWord, tailWord_7287257, baseEnd_7287257] using wordTrace_append hprefix tailTrace_7287257
  have hstable : (prefixWord ++ tailWord_7287257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287257).length < 2 ^ (prefixWord ++ tailWord_7287257).sum := by decide
  have hdescent : baseEnd_7287257 < baseStart_7287257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287274 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_7287274 : Nat := 118140960795 + 7287274 * 2 ^ 59
def prefixEnd_7287274 : Nat := 4983230072969 + 3 ^ 40 * 7287274 * 2
def baseEnd_7287274 : Nat := 3741874223012426740661443

theorem tailTrace_7287274 : CollatzResearch.WordTrace tailWord_7287274 prefixEnd_7287274 3741874223012426740661443 := by
  unfold tailWord_7287274
  simp only [CollatzResearch.WordTrace]
  refine ⟨66447179550364585039811219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177192478800972226772829917 66447179550364585039811219)
  ·
    refine ⟨99670769325546877559716829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66447179550364585039811219 99670769325546877559716829)
    ·
      refine ⟨37376538497080079084893811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99670769325546877559716829 37376538497080079084893811)
      ·
        refine ⟨56064807745620118627340717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37376538497080079084893811 56064807745620118627340717)
        ·
          refine ⟨21024302904607544485252769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56064807745620118627340717 21024302904607544485252769)
          ·
            refine ⟨15768227178455658363939577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21024302904607544485252769 15768227178455658363939577)
            ·
              refine ⟨11826170383841743772954683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15768227178455658363939577 11826170383841743772954683)
              ·
                refine ⟨17739255575762615659432025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826170383841743772954683 17739255575762615659432025)
                ·
                  refine ⟨13304441681821961744574019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17739255575762615659432025 13304441681821961744574019)
                  ·
                    refine ⟨19956662522732942616861029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13304441681821961744574019 19956662522732942616861029)
                    ·
                      refine ⟨3741874223012426740661443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19956662522732942616861029 3741874223012426740661443)
                      ·
                        rfl

theorem cell23_7287274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_7287274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287274 prefixEnd_7287274 := by exact prefixLift 7287274
  have htrace : WordTrace (prefixWord ++ tailWord_7287274) baseStart_7287274 baseEnd_7287274 := by
    simpa [prefixWord, tailWord_7287274, baseEnd_7287274] using wordTrace_append hprefix tailTrace_7287274
  have hstable : (prefixWord ++ tailWord_7287274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287274).length < 2 ^ (prefixWord ++ tailWord_7287274).sum := by decide
  have hdescent : baseEnd_7287274 < baseStart_7287274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287297 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 6]
def baseStart_7287297 : Nat := 118140960795 + 7287297 * 2 ^ 59
def prefixEnd_7287297 : Nat := 4983230072969 + 3 ^ 40 * 7287297 * 2
def baseEnd_7287297 : Nat := 415765114785275572297093

theorem tailTrace_7287297 : CollatzResearch.WordTrace tailWord_7287297 prefixEnd_7287297 415765114785275572297093 := by
  unfold tailWord_7287297
  simp only [CollatzResearch.WordTrace]
  refine ⟨265789557080375015087332145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177193038053583343391554763 265789557080375015087332145)
  ·
    refine ⟨199342167810281261315499109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265789557080375015087332145 199342167810281261315499109)
    ·
      refine ⟨37376656464427736496656083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199342167810281261315499109 37376656464427736496656083)
      ·
        refine ⟨56064984696641604744984125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37376656464427736496656083 56064984696641604744984125)
        ·
          refine ⟨21024369261240601779369047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56064984696641604744984125 21024369261240601779369047)
          ·
            refine ⟨31536553891860902669053571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21024369261240601779369047 31536553891860902669053571)
            ·
              refine ⟨47304830837791354003580357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31536553891860902669053571 47304830837791354003580357)
              ·
                refine ⟨8869655782085878875671317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47304830837791354003580357 8869655782085878875671317)
                ·
                  refine ⟨415765114785275572297093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8869655782085878875671317 415765114785275572297093)
                  ·
                    rfl

theorem cell23_7287297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 6].length) (baseStart_7287297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287297 prefixEnd_7287297 := by exact prefixLift 7287297
  have htrace : WordTrace (prefixWord ++ tailWord_7287297) baseStart_7287297 baseEnd_7287297 := by
    simpa [prefixWord, tailWord_7287297, baseEnd_7287297] using wordTrace_append hprefix tailTrace_7287297
  have hstable : (prefixWord ++ tailWord_7287297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287297).length < 2 ^ (prefixWord ++ tailWord_7287297).sum := by decide
  have hdescent : baseEnd_7287297 < baseStart_7287297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287301 : List Nat := [1, 3, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_7287301 : Nat := 118140960795 + 7287301 * 2 ^ 59
def prefixEnd_7287301 : Nat := 4983230072969 + 3 ^ 40 * 7287301 * 2
def baseEnd_7287301 : Nat := 1247296028996699378341273

theorem tailTrace_7287301 : CollatzResearch.WordTrace tailWord_7287301 prefixEnd_7287301 1247296028996699378341273 := by
  unfold tailWord_7287301
  simp only [CollatzResearch.WordTrace]
  refine ⟨265789702972360523770477757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177193135314907015846985171 265789702972360523770477757)
  ·
    refine ⟨99671138614635196413929159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265789702972360523770477757 99671138614635196413929159)
    ·
      refine ⟨149506707921952794620893739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99671138614635196413929159 149506707921952794620893739)
      ·
        refine ⟨224260061882929191931340609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149506707921952794620893739 224260061882929191931340609)
        ·
          refine ⟨168195046412196893948505457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224260061882929191931340609 168195046412196893948505457)
          ·
            refine ⟨126146284809147670461379093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168195046412196893948505457 126146284809147670461379093)
            ·
              refine ⟨5913107100428797052877145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126146284809147670461379093 5913107100428797052877145)
              ·
                refine ⟨4434830325321597789657859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5913107100428797052877145 4434830325321597789657859)
                ·
                  refine ⟨6652245487982396684486789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434830325321597789657859 6652245487982396684486789)
                  ·
                    refine ⟨1247296028996699378341273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652245487982396684486789 1247296028996699378341273)
                    ·
                      rfl

theorem cell23_7287301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_7287301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287301 prefixEnd_7287301 := by exact prefixLift 7287301
  have htrace : WordTrace (prefixWord ++ tailWord_7287301) baseStart_7287301 baseEnd_7287301 := by
    simpa [prefixWord, tailWord_7287301, baseEnd_7287301] using wordTrace_append hprefix tailTrace_7287301
  have hstable : (prefixWord ++ tailWord_7287301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287301).length < 2 ^ (prefixWord ++ tailWord_7287301).sum := by decide
  have hdescent : baseEnd_7287301 < baseStart_7287301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287324 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_7287324 : Nat := 118140960795 + 7287324 * 2 ^ 59
def prefixEnd_7287324 : Nat := 4983230072969 + 3 ^ 40 * 7287324 * 2
def baseEnd_7287324 : Nat := 3741899897045151545036213

theorem tailTrace_7287324 : CollatzResearch.WordTrace tailWord_7287324 prefixEnd_7287324 3741899897045151545036213 := by
  unfold tailWord_7287324
  simp only [CollatzResearch.WordTrace]
  refine ⟨132895270925638599349282513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177193694567518132465710017 132895270925638599349282513)
  ·
    refine ⟨99671453194228949511961885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132895270925638599349282513 99671453194228949511961885)
    ·
      refine ⟨37376794947835856066985707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99671453194228949511961885 37376794947835856066985707)
      ·
        refine ⟨56065192421753784100478561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37376794947835856066985707 56065192421753784100478561)
        ·
          refine ⟨42048894316315338075358921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56065192421753784100478561 42048894316315338075358921)
          ·
            refine ⟨31536670737236503556519191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42048894316315338075358921 31536670737236503556519191)
            ·
              refine ⟨47305006105854755334778787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31536670737236503556519191 47305006105854755334778787)
              ·
                refine ⟨70957509158782133002168181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47305006105854755334778787 70957509158782133002168181)
                ·
                  refine ⟨6652266483635824968953267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70957509158782133002168181 6652266483635824968953267)
                  ·
                    refine ⟨9978399725453737453429901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652266483635824968953267 9978399725453737453429901)
                    ·
                      refine ⟨3741899897045151545036213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978399725453737453429901 3741899897045151545036213)
                      ·
                        rfl

theorem cell23_7287324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_7287324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287324 prefixEnd_7287324 := by exact prefixLift 7287324
  have htrace : WordTrace (prefixWord ++ tailWord_7287324) baseStart_7287324 baseEnd_7287324 := by
    simpa [prefixWord, tailWord_7287324, baseEnd_7287324] using wordTrace_append hprefix tailTrace_7287324
  have hstable : (prefixWord ++ tailWord_7287324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287324).length < 2 ^ (prefixWord ++ tailWord_7287324).sum := by decide
  have hdescent : baseEnd_7287324 < baseStart_7287324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287327 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 1, 5]
def baseStart_7287327 : Nat := 118140960795 + 7287327 * 2 ^ 59
def prefixEnd_7287327 : Nat := 4983230072969 + 3 ^ 40 * 7287327 * 2
def baseEnd_7287327 : Nat := 1247300479162371677766233

theorem tailTrace_7287327 : CollatzResearch.WordTrace tailWord_7287327 prefixEnd_7287327 1247300479162371677766233 := by
  unfold tailWord_7287327
  simp only [CollatzResearch.WordTrace]
  refine ⟨265790651270266330210924235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177193767513510886807282823 265790651270266330210924235)
  ·
    refine ⟨398685976905399495316386353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265790651270266330210924235 398685976905399495316386353)
    ·
      refine ⟨299014482679049621487289765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398685976905399495316386353 299014482679049621487289765)
      ·
        refine ⟨56065215502321804028866831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299014482679049621487289765 56065215502321804028866831)
        ·
          refine ⟨84097823253482706043300247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56065215502321804028866831 84097823253482706043300247)
          ·
            refine ⟨126146734880224059064950371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84097823253482706043300247 126146734880224059064950371)
            ·
              refine ⟨189220102320336088597425557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126146734880224059064950371 189220102320336088597425557)
              ·
                refine ⟨8869692296265754153004323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189220102320336088597425557 8869692296265754153004323)
                ·
                  refine ⟨13304538444398631229506485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869692296265754153004323 13304538444398631229506485)
                  ·
                    refine ⟨1247300479162371677766233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13304538444398631229506485 1247300479162371677766233)
                    ·
                      rfl

theorem cell23_7287327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_7287327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287327 prefixEnd_7287327 := by exact prefixLift 7287327
  have htrace : WordTrace (prefixWord ++ tailWord_7287327) baseStart_7287327 baseEnd_7287327 := by
    simpa [prefixWord, tailWord_7287327, baseEnd_7287327] using wordTrace_append hprefix tailTrace_7287327
  have hstable : (prefixWord ++ tailWord_7287327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287327).length < 2 ^ (prefixWord ++ tailWord_7287327).sum := by decide
  have hdescent : baseEnd_7287327 < baseStart_7287327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287328 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7287328 : Nat := 118140960795 + 7287328 * 2 ^ 59
def prefixEnd_7287328 : Nat := 4983230072969 + 3 ^ 40 * 7287328 * 2
def baseEnd_7287328 : Nat := 3741901950967769529386195

theorem tailTrace_7287328 : CollatzResearch.WordTrace tailWord_7287328 prefixEnd_7287328 3741901950967769529386195 := by
  unfold tailWord_7287328
  simp only [CollatzResearch.WordTrace]
  refine ⟨132895343871631353690855319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177193791828841804921140425 132895343871631353690855319)
  ·
    refine ⟨199343015807447030536282979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132895343871631353690855319 199343015807447030536282979)
    ·
      refine ⟨299014523711170545804424469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199343015807447030536282979 299014523711170545804424469)
      ·
        refine ⟨14016305798961119334582397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 299014523711170545804424469 14016305798961119334582397)
        ·
          refine ⟨5256114674610419750468399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14016305798961119334582397 5256114674610419750468399)
          ·
            refine ⟨7884172011915629625702599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256114674610419750468399 7884172011915629625702599)
            ·
              refine ⟨11826258017873444438553899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884172011915629625702599 11826258017873444438553899)
              ·
                refine ⟨17739387026810166657830849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826258017873444438553899 17739387026810166657830849)
                ·
                  refine ⟨13304540270107624993373137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17739387026810166657830849 13304540270107624993373137)
                  ·
                    refine ⟨9978405202580718745029853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13304540270107624993373137 9978405202580718745029853)
                    ·
                      refine ⟨3741901950967769529386195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978405202580718745029853 3741901950967769529386195)
                      ·
                        rfl

theorem cell23_7287328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7287328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287328 prefixEnd_7287328 := by exact prefixLift 7287328
  have htrace : WordTrace (prefixWord ++ tailWord_7287328) baseStart_7287328 baseEnd_7287328 := by
    simpa [prefixWord, tailWord_7287328, baseEnd_7287328] using wordTrace_append hprefix tailTrace_7287328
  have hstable : (prefixWord ++ tailWord_7287328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287328).length < 2 ^ (prefixWord ++ tailWord_7287328).sum := by decide
  have hdescent : baseEnd_7287328 < baseStart_7287328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287335 : List Nat := [1, 1, 7, 2, 1, 1, 2, 3, 1, 4]
def baseStart_7287335 : Nat := 118140960795 + 7287335 * 2 ^ 59
def prefixEnd_7287335 : Nat := 4983230072969 + 3 ^ 40 * 7287335 * 2
def baseEnd_7287335 : Nat := 1247301848444117000666221

theorem tailTrace_7287335 : CollatzResearch.WordTrace tailWord_7287335 prefixEnd_7287335 1247301848444117000666221 := by
  unfold tailWord_7287335
  simp only [CollatzResearch.WordTrace]
  refine ⟨265790943054237347577215459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177193962036158231718143639 265790943054237347577215459)
  ·
    refine ⟨398686414581356021365823189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265790943054237347577215459 398686414581356021365823189)
    ·
      refine ⟨9344212841750531750761481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 398686414581356021365823189 9344212841750531750761481)
      ·
        refine ⟨7008159631312898813071111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9344212841750531750761481 7008159631312898813071111)
        ·
          refine ⟨10512239446969348219606667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008159631312898813071111 10512239446969348219606667)
          ·
            refine ⟨15768359170454022329410001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512239446969348219606667 15768359170454022329410001)
            ·
              refine ⟨11826269377840516747057501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15768359170454022329410001 11826269377840516747057501)
              ·
                refine ⟨4434851016690193780146563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11826269377840516747057501 4434851016690193780146563)
                ·
                  refine ⟨6652276525035290670219845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434851016690193780146563 6652276525035290670219845)
                  ·
                    refine ⟨1247301848444117000666221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652276525035290670219845 1247301848444117000666221)
                    ·
                      rfl

theorem cell23_7287335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_7287335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287335 prefixEnd_7287335 := by exact prefixLift 7287335
  have htrace : WordTrace (prefixWord ++ tailWord_7287335) baseStart_7287335 baseEnd_7287335 := by
    simpa [prefixWord, tailWord_7287335, baseEnd_7287335] using wordTrace_append hprefix tailTrace_7287335
  have hstable : (prefixWord ++ tailWord_7287335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287335).length < 2 ^ (prefixWord ++ tailWord_7287335).sum := by decide
  have hdescent : baseEnd_7287335 < baseStart_7287335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287344 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 1, 5]
def baseStart_7287344 : Nat := 118140960795 + 7287344 * 2 ^ 59
def prefixEnd_7287344 : Nat := 4983230072969 + 3 ^ 40 * 7287344 * 2
def baseEnd_7287344 : Nat := 1247303388886080488928707

theorem tailTrace_7287344 : CollatzResearch.WordTrace tailWord_7287344 prefixEnd_7287344 1247303388886080488928707 := by
  unfold tailWord_7287344
  simp only [CollatzResearch.WordTrace]
  refine ⟨132895635655602371057146543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177194180874136494742862057 132895635655602371057146543)
  ·
    refine ⟨199343453483403556585719815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132895635655602371057146543 199343453483403556585719815)
    ·
      refine ⟨299015180225105334878579723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199343453483403556585719815 299015180225105334878579723)
      ·
        refine ⟨448522770337658002317869585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299015180225105334878579723 448522770337658002317869585)
        ·
          refine ⟨336392077753243501738402189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448522770337658002317869585 336392077753243501738402189)
          ·
            refine ⟨126147029157466313151900821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336392077753243501738402189 126147029157466313151900821)
            ·
              refine ⟨5913141991756233428995351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126147029157466313151900821 5913141991756233428995351)
              ·
                refine ⟨8869712987634350143493027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913141991756233428995351 8869712987634350143493027)
                ·
                  refine ⟨13304569481451525215239541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869712987634350143493027 13304569481451525215239541)
                  ·
                    refine ⟨1247303388886080488928707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13304569481451525215239541 1247303388886080488928707)
                    ·
                      rfl

theorem cell23_7287344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 1, 5].length) (baseStart_7287344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287344 prefixEnd_7287344 := by exact prefixLift 7287344
  have htrace : WordTrace (prefixWord ++ tailWord_7287344) baseStart_7287344 baseEnd_7287344 := by
    simpa [prefixWord, tailWord_7287344, baseEnd_7287344] using wordTrace_append hprefix tailTrace_7287344
  have hstable : (prefixWord ++ tailWord_7287344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287344).length < 2 ^ (prefixWord ++ tailWord_7287344).sum := by decide
  have hdescent : baseEnd_7287344 < baseStart_7287344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287348 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 6]
def baseStart_7287348 : Nat := 118140960795 + 7287348 * 2 ^ 59
def prefixEnd_7287348 : Nat := 4983230072969 + 3 ^ 40 * 7287348 * 2
def baseEnd_7287348 : Nat := 415768024508984383459567

theorem tailTrace_7287348 : CollatzResearch.WordTrace tailWord_7287348 prefixEnd_7287348 415768024508984383459567 := by
  unfold tailWord_7287348
  simp only [CollatzResearch.WordTrace]
  refine ⟨132895708601595125398719349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177194278135460167198292465 132895708601595125398719349)
  ·
    refine ⟨12458972681399543006129939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132895708601595125398719349 12458972681399543006129939)
    ·
      refine ⟨18688459022099314509194909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458972681399543006129939 18688459022099314509194909)
      ·
        refine ⟨7008172133287242940948091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18688459022099314509194909 7008172133287242940948091)
        ·
          refine ⟨10512258199930864411422137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008172133287242940948091 10512258199930864411422137)
          ·
            refine ⟨7884193649948148308566603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10512258199930864411422137 7884193649948148308566603)
            ·
              refine ⟨11826290474922222462849905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884193649948148308566603 11826290474922222462849905)
              ·
                refine ⟨8869717856191666847137429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11826290474922222462849905 8869717856191666847137429)
                ·
                  refine ⟨415768024508984383459567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8869717856191666847137429 415768024508984383459567)
                  ·
                    rfl

theorem cell23_7287348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_7287348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287348 prefixEnd_7287348 := by exact prefixLift 7287348
  have htrace : WordTrace (prefixWord ++ tailWord_7287348) baseStart_7287348 baseEnd_7287348 := by
    simpa [prefixWord, tailWord_7287348, baseEnd_7287348] using wordTrace_append hprefix tailTrace_7287348
  have hstable : (prefixWord ++ tailWord_7287348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287348).length < 2 ^ (prefixWord ++ tailWord_7287348).sum := by decide
  have hdescent : baseEnd_7287348 < baseStart_7287348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287367 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_7287367 : Nat := 118140960795 + 7287367 * 2 ^ 59
def prefixEnd_7287367 : Nat := 4983230072969 + 3 ^ 40 * 7287367 * 2
def baseEnd_7287367 : Nat := 3741921976713294876798515

theorem tailTrace_7287367 : CollatzResearch.WordTrace tailWord_7287367 prefixEnd_7287367 3741921976713294876798515 := by
  unfold tailWord_7287367
  simp only [CollatzResearch.WordTrace]
  refine ⟨265792110190121417042380355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177194740126747611361586903 265792110190121417042380355)
  ·
    refine ⟨398688165285182125563570533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265792110190121417042380355 398688165285182125563570533)
    ·
      refine ⟨74754030990971648543169475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398688165285182125563570533 74754030990971648543169475)
      ·
        refine ⟨112131046486457472814754213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74754030990971648543169475 112131046486457472814754213)
        ·
          refine ⟨21024571216210776152766415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112131046486457472814754213 21024571216210776152766415)
          ·
            refine ⟨31536856824316164229149623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21024571216210776152766415 31536856824316164229149623)
            ·
              refine ⟨47305285236474246343724435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31536856824316164229149623 47305285236474246343724435)
              ·
                refine ⟨70957927854711369515586653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47305285236474246343724435 70957927854711369515586653)
                ·
                  refine ⟨26609222945516763568344995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70957927854711369515586653 26609222945516763568344995)
                  ·
                    refine ⟨39913834418275145352517493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26609222945516763568344995 39913834418275145352517493)
                    ·
                      refine ⟨3741921976713294876798515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39913834418275145352517493 3741921976713294876798515)
                      ·
                        rfl

theorem cell23_7287367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_7287367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287367 prefixEnd_7287367 := by exact prefixLift 7287367
  have htrace : WordTrace (prefixWord ++ tailWord_7287367) baseStart_7287367 baseEnd_7287367 := by
    simpa [prefixWord, tailWord_7287367, baseEnd_7287367] using wordTrace_append hprefix tailTrace_7287367
  have hstable : (prefixWord ++ tailWord_7287367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287367).length < 2 ^ (prefixWord ++ tailWord_7287367).sum := by decide
  have hdescent : baseEnd_7287367 < baseStart_7287367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287374 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_7287374 : Nat := 118140960795 + 7287374 * 2 ^ 59
def prefixEnd_7287374 : Nat := 4983230072969 + 3 ^ 40 * 7287374 * 2
def baseEnd_7287374 : Nat := 1247308523692625449803661

theorem tailTrace_7287374 : CollatzResearch.WordTrace tailWord_7287374 prefixEnd_7287374 1247308523692625449803661 := by
  unfold tailWord_7287374
  simp only [CollatzResearch.WordTrace]
  refine ⟨33224045687637007154735647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177194910334064038158590117 33224045687637007154735647)
  ·
    refine ⟨49836068531455510732103471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33224045687637007154735647 49836068531455510732103471)
    ·
      refine ⟨74754102797183266098155207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49836068531455510732103471 74754102797183266098155207)
      ·
        refine ⟨112131154195774899147232811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74754102797183266098155207 112131154195774899147232811)
        ·
          refine ⟨168196731293662348720849217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112131154195774899147232811 168196731293662348720849217)
          ·
            refine ⟨126147548470246761540636913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168196731293662348720849217 126147548470246761540636913)
            ·
              refine ⟨94610661352685071155477685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126147548470246761540636913 94610661352685071155477685)
              ·
                refine ⟨8869749501814225420826033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94610661352685071155477685 8869749501814225420826033)
                ·
                  refine ⟨6652312126360669065619525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8869749501814225420826033 6652312126360669065619525)
                  ·
                    refine ⟨1247308523692625449803661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652312126360669065619525 1247308523692625449803661)
                    ·
                      rfl

theorem cell23_7287374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_7287374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287374 prefixEnd_7287374 := by exact prefixLift 7287374
  have htrace : WordTrace (prefixWord ++ tailWord_7287374) baseStart_7287374 baseEnd_7287374 := by
    simpa [prefixWord, tailWord_7287374, baseEnd_7287374] using wordTrace_append hprefix tailTrace_7287374
  have hstable : (prefixWord ++ tailWord_7287374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287374).length < 2 ^ (prefixWord ++ tailWord_7287374).sum := by decide
  have hdescent : baseEnd_7287374 < baseStart_7287374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287377 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_7287377 : Nat := 118140960795 + 7287377 * 2 ^ 59
def prefixEnd_7287377 : Nat := 4983230072969 + 3 ^ 40 * 7287377 * 2
def baseEnd_7287377 : Nat := 3741927111519839837673469

theorem tailTrace_7287377 : CollatzResearch.WordTrace tailWord_7287377 prefixEnd_7287377 3741927111519839837673469 := by
  unfold tailWord_7287377
  simp only [CollatzResearch.WordTrace]
  refine ⟨265792474920085188750244385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177194983280056792500162923 265792474920085188750244385)
  ·
    refine ⟨199344356190063891562683289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265792474920085188750244385 199344356190063891562683289)
    ·
      refine ⟨149508267142547918672012467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199344356190063891562683289 149508267142547918672012467)
      ·
        refine ⟨224262400713821878008018701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149508267142547918672012467 224262400713821878008018701)
        ·
          refine ⟨84098400267683204253007013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224262400713821878008018701 84098400267683204253007013)
          ·
            refine ⟨15768450050190600797438815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84098400267683204253007013 15768450050190600797438815)
            ·
              refine ⟨23652675075285901196158223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15768450050190600797438815 23652675075285901196158223)
              ·
                refine ⟨35479012612928851794237335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23652675075285901196158223 35479012612928851794237335)
                ·
                  refine ⟨53218518919393277691356003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35479012612928851794237335 53218518919393277691356003)
                  ·
                    refine ⟨79827778379089916537034005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53218518919393277691356003 79827778379089916537034005)
                    ·
                      refine ⟨3741927111519839837673469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79827778379089916537034005 3741927111519839837673469)
                      ·
                        rfl

theorem cell23_7287377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_7287377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287377 prefixEnd_7287377 := by exact prefixLift 7287377
  have htrace : WordTrace (prefixWord ++ tailWord_7287377) baseStart_7287377 baseEnd_7287377 := by
    simpa [prefixWord, tailWord_7287377, baseEnd_7287377] using wordTrace_append hprefix tailTrace_7287377
  have hstable : (prefixWord ++ tailWord_7287377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287377).length < 2 ^ (prefixWord ++ tailWord_7287377).sum := by decide
  have hdescent : baseEnd_7287377 < baseStart_7287377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287381 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_7287381 : Nat := 118140960795 + 7287381 * 2 ^ 59
def prefixEnd_7287381 : Nat := 4983230072969 + 3 ^ 40 * 7287381 * 2
def baseEnd_7287381 : Nat := 3741929165442457822023451

theorem tailTrace_7287381 : CollatzResearch.WordTrace tailWord_7287381 prefixEnd_7287381 3741929165442457822023451 := by
  unfold tailWord_7287381
  simp only [CollatzResearch.WordTrace]
  refine ⟨265792620812070697433389997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177195080541380464955593331 265792620812070697433389997)
  ·
    refine ⟨99672232804526511537521249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265792620812070697433389997 99672232804526511537521249)
    ·
      refine ⟨74754174603394883653140937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99672232804526511537521249 74754174603394883653140937)
      ·
        refine ⟨56065630952546162739855703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74754174603394883653140937 56065630952546162739855703)
        ·
          refine ⟨84098446428819244109783555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56065630952546162739855703 84098446428819244109783555)
          ·
            refine ⟨126147669643228866164675333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84098446428819244109783555 126147669643228866164675333)
            ·
              refine ⟨23652688058105412405876625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126147669643228866164675333 23652688058105412405876625)
              ·
                refine ⟨17739516043579059304407469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23652688058105412405876625 17739516043579059304407469)
                ·
                  refine ⟨6652318516342147239152801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17739516043579059304407469 6652318516342147239152801)
                  ·
                    refine ⟨4989238887256610429364601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6652318516342147239152801 4989238887256610429364601)
                    ·
                      refine ⟨3741929165442457822023451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989238887256610429364601 3741929165442457822023451)
                      ·
                        rfl

theorem cell23_7287381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_7287381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287381 prefixEnd_7287381 := by exact prefixLift 7287381
  have htrace : WordTrace (prefixWord ++ tailWord_7287381) baseStart_7287381 baseEnd_7287381 := by
    simpa [prefixWord, tailWord_7287381, baseEnd_7287381] using wordTrace_append hprefix tailTrace_7287381
  have hstable : (prefixWord ++ tailWord_7287381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287381).length < 2 ^ (prefixWord ++ tailWord_7287381).sum := by decide
  have hdescent : baseEnd_7287381 < baseStart_7287381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287384 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_7287384 : Nat := 118140960795 + 7287384 * 2 ^ 59
def prefixEnd_7287384 : Nat := 4983230072969 + 3 ^ 40 * 7287384 * 2
def baseEnd_7287384 : Nat := 3741930705884421310285937

theorem tailTrace_7287384 : CollatzResearch.WordTrace tailWord_7287384 prefixEnd_7287384 3741930705884421310285937 := by
  unfold tailWord_7287384
  simp only [CollatzResearch.WordTrace]
  refine ⟨132896365115529914472874603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177195153487373219297166137 132896365115529914472874603)
  ·
    refine ⟨199344547673294871709311905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132896365115529914472874603 199344547673294871709311905)
    ·
      refine ⟨149508410754971153781983929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199344547673294871709311905 149508410754971153781983929)
      ·
        refine ⟨112131308066228365336487947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149508410754971153781983929 112131308066228365336487947)
        ·
          refine ⟨168196962099342548004731921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112131308066228365336487947 168196962099342548004731921)
          ·
            refine ⟨126147721574506911003548941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168196962099342548004731921 126147721574506911003548941)
            ·
              refine ⟨47305395590440091626330853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126147721574506911003548941 47305395590440091626330853)
              ·
                refine ⟨8869761673207517179937035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47305395590440091626330853 8869761673207517179937035)
                ·
                  refine ⟨13304642509811275769905553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869761673207517179937035 13304642509811275769905553)
                  ·
                    refine ⟨9978481882358456827429165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13304642509811275769905553 9978481882358456827429165)
                    ·
                      refine ⟨3741930705884421310285937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978481882358456827429165 3741930705884421310285937)
                      ·
                        rfl

theorem cell23_7287384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_7287384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287384 prefixEnd_7287384 := by exact prefixLift 7287384
  have htrace : WordTrace (prefixWord ++ tailWord_7287384) baseStart_7287384 baseEnd_7287384 := by
    simpa [prefixWord, tailWord_7287384, baseEnd_7287384] using wordTrace_append hprefix tailTrace_7287384
  have hstable : (prefixWord ++ tailWord_7287384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287384).length < 2 ^ (prefixWord ++ tailWord_7287384).sum := by decide
  have hdescent : baseEnd_7287384 < baseStart_7287384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287431 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_7287431 : Nat := 118140960795 + 7287431 * 2 ^ 59
def prefixEnd_7287431 : Nat := 4983230072969 + 3 ^ 40 * 7287431 * 2
def baseEnd_7287431 : Nat := 3741954839475182626398221

theorem tailTrace_7287431 : CollatzResearch.WordTrace tailWord_7287431 prefixEnd_7287431 3741954839475182626398221 := by
  unfold tailWord_7287431
  simp only [CollatzResearch.WordTrace]
  refine ⟨265794444461889555972710147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177196296307926370648473431 265794444461889555972710147)
  ·
    refine ⟨398691666692834333959065221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265794444461889555972710147 398691666692834333959065221)
    ·
      refine ⟨74754687504906437617324729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398691666692834333959065221 74754687504906437617324729)
      ·
        refine ⟨56066015628679828212993547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74754687504906437617324729 56066015628679828212993547)
        ·
          refine ⟨84099023443019742319490321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56066015628679828212993547 84099023443019742319490321)
          ·
            refine ⟨63074267582264806739617741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84099023443019742319490321 63074267582264806739617741)
            ·
              refine ⟨23652850343349302527356653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63074267582264806739617741 23652850343349302527356653)
              ·
                refine ⟨8869818878755988447758745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23652850343349302527356653 8869818878755988447758745)
                ·
                  refine ⟨6652364159066991335819059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8869818878755988447758745 6652364159066991335819059)
                  ·
                    refine ⟨9978546238600487003728589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652364159066991335819059 9978546238600487003728589)
                    ·
                      refine ⟨3741954839475182626398221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978546238600487003728589 3741954839475182626398221)
                      ·
                        rfl

theorem cell23_7287431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_7287431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287431 prefixEnd_7287431 := by exact prefixLift 7287431
  have htrace : WordTrace (prefixWord ++ tailWord_7287431) baseStart_7287431 baseEnd_7287431 := by
    simpa [prefixWord, tailWord_7287431, baseEnd_7287431] using wordTrace_append hprefix tailTrace_7287431
  have hstable : (prefixWord ++ tailWord_7287431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287431).length < 2 ^ (prefixWord ++ tailWord_7287431).sum := by decide
  have hdescent : baseEnd_7287431 < baseStart_7287431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287466 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7287466 : Nat := 118140960795 + 7287466 * 2 ^ 59
def prefixEnd_7287466 : Nat := 4983230072969 + 3 ^ 40 * 7287466 * 2
def baseEnd_7287466 : Nat := 3741972811298089989460561

theorem tailTrace_7287466 : CollatzResearch.WordTrace tailWord_7287466 prefixEnd_7287466 3741972811298089989460561 := by
  unfold tailWord_7287466
  simp only [CollatzResearch.WordTrace]
  refine ⟨66448930254190689237558563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177197147344508504633489501 66448930254190689237558563)
  ·
    refine ⟨99673395381286033856337845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66448930254190689237558563 99673395381286033856337845)
    ·
      refine ⟨9344380816995565674031673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99673395381286033856337845 9344380816995565674031673)
      ·
        refine ⟨7008285612746674255523755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9344380816995565674031673 7008285612746674255523755)
        ·
          refine ⟨10512428419120011383285633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008285612746674255523755 10512428419120011383285633)
          ·
            refine ⟨7884321314340008537464225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10512428419120011383285633 7884321314340008537464225)
            ·
              refine ⟨5913240985755006403098169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7884321314340008537464225 5913240985755006403098169)
              ·
                refine ⟨4434930739316254802323627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5913240985755006403098169 4434930739316254802323627)
                ·
                  refine ⟨6652396108974382203485441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434930739316254802323627 6652396108974382203485441)
                  ·
                    refine ⟨4989297081730786652614081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6652396108974382203485441 4989297081730786652614081)
                    ·
                      refine ⟨3741972811298089989460561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989297081730786652614081 3741972811298089989460561)
                      ·
                        rfl

theorem cell23_7287466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7287466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287466 prefixEnd_7287466 := by exact prefixLift 7287466
  have htrace : WordTrace (prefixWord ++ tailWord_7287466) baseStart_7287466 baseEnd_7287466 := by
    simpa [prefixWord, tailWord_7287466, baseEnd_7287466] using wordTrace_append hprefix tailTrace_7287466
  have hstable : (prefixWord ++ tailWord_7287466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287466).length < 2 ^ (prefixWord ++ tailWord_7287466).sum := by decide
  have hdescent : baseEnd_7287466 < baseStart_7287466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287484 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7287484 : Nat := 118140960795 + 7287484 * 2 ^ 59
def prefixEnd_7287484 : Nat := 4983230072969 + 3 ^ 40 * 7287484 * 2
def baseEnd_7287484 : Nat := 3741982053949870919035477

theorem tailTrace_7287484 : CollatzResearch.WordTrace tailWord_7287484 prefixEnd_7287484 3741982053949870919035477 := by
  unfold tailWord_7287484
  simp only [CollatzResearch.WordTrace]
  refine ⟨132898188765348773012194753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177197585020465030682926337 132898188765348773012194753)
  ·
    refine ⟨99673641574011579759146065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132898188765348773012194753 99673641574011579759146065)
    ·
      refine ⟨74755231180508684819359549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99673641574011579759146065 74755231180508684819359549)
      ·
        refine ⟨28033211692690756807259831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74755231180508684819359549 28033211692690756807259831)
        ·
          refine ⟨42049817539036135210889747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28033211692690756807259831 42049817539036135210889747)
          ·
            refine ⟨63074726308554202816334621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42049817539036135210889747 63074726308554202816334621)
            ·
              refine ⟨23653022365707826056125483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63074726308554202816334621 23653022365707826056125483)
              ·
                refine ⟨35479533548561739084188225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23653022365707826056125483 35479533548561739084188225)
                ·
                  refine ⟨26609650161421304313141169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35479533548561739084188225 26609650161421304313141169)
                  ·
                    refine ⟨19957237621065978234855877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26609650161421304313141169 19957237621065978234855877)
                    ·
                      refine ⟨3741982053949870919035477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19957237621065978234855877 3741982053949870919035477)
                      ·
                        rfl

theorem cell23_7287484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7287484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287484 prefixEnd_7287484 := by exact prefixLift 7287484
  have htrace : WordTrace (prefixWord ++ tailWord_7287484) baseStart_7287484 baseEnd_7287484 := by
    simpa [prefixWord, tailWord_7287484, baseEnd_7287484] using wordTrace_append hprefix tailTrace_7287484
  have hstable : (prefixWord ++ tailWord_7287484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287484).length < 2 ^ (prefixWord ++ tailWord_7287484).sum := by decide
  have hdescent : baseEnd_7287484 < baseStart_7287484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287488 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 2, 2, 2]
def baseStart_7287488 : Nat := 118140960795 + 7287488 * 2 ^ 59
def prefixEnd_7287488 : Nat := 4983230072969 + 3 ^ 40 * 7287488 * 2
def baseEnd_7287488 : Nat := 3741984107872488903385459

theorem tailTrace_7287488 : CollatzResearch.WordTrace tailWord_7287488 prefixEnd_7287488 3741984107872488903385459 := by
  unfold tailWord_7287488
  simp only [CollatzResearch.WordTrace]
  refine ⟨132898261711341527353767559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177197682281788703138356745 132898261711341527353767559)
  ·
    refine ⟨199347392567012291030651339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132898261711341527353767559 199347392567012291030651339)
    ·
      refine ⟨299021088850518436545977009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199347392567012291030651339 299021088850518436545977009)
      ·
        refine ⟨224265816637888827409482757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299021088850518436545977009 224265816637888827409482757)
        ·
          refine ⟨42049840619604155139278017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224265816637888827409482757 42049840619604155139278017)
          ·
            refine ⟨31537380464703116354458513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42049840619604155139278017 31537380464703116354458513)
            ·
              refine ⟨23653035348527337265843885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31537380464703116354458513 23653035348527337265843885)
              ·
                refine ⟨8869888255697751474691457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23653035348527337265843885 8869888255697751474691457)
                ·
                  refine ⟨6652416191773313606018593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8869888255697751474691457 6652416191773313606018593)
                  ·
                    refine ⟨4989312143829985204513945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6652416191773313606018593 4989312143829985204513945)
                    ·
                      refine ⟨3741984107872488903385459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989312143829985204513945 3741984107872488903385459)
                      ·
                        rfl

theorem cell23_7287488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_7287488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287488 prefixEnd_7287488 := by exact prefixLift 7287488
  have htrace : WordTrace (prefixWord ++ tailWord_7287488) baseStart_7287488 baseEnd_7287488 := by
    simpa [prefixWord, tailWord_7287488, baseEnd_7287488] using wordTrace_append hprefix tailTrace_7287488
  have hstable : (prefixWord ++ tailWord_7287488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287488).length < 2 ^ (prefixWord ++ tailWord_7287488).sum := by decide
  have hdescent : baseEnd_7287488 < baseStart_7287488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287509 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7287509 : Nat := 118140960795 + 7287509 * 2 ^ 59
def prefixEnd_7287509 : Nat := 4983230072969 + 3 ^ 40 * 7287509 * 2
def baseEnd_7287509 : Nat := 3741994890966233321222863

theorem tailTrace_7287509 : CollatzResearch.WordTrace tailWord_7287509 prefixEnd_7287509 3741994890966233321222863 := by
  unfold tailWord_7287509
  simp only [CollatzResearch.WordTrace]
  refine ⟨265797289355606975294049581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177198192903737983529366387 265797289355606975294049581)
  ·
    refine ⟨99673983508352615735268593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265797289355606975294049581 99673983508352615735268593)
    ·
      refine ⟨74755487631264461801451445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99673983508352615735268593 74755487631264461801451445)
      ·
        refine ⟨7008326965431043293886073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74755487631264461801451445 7008326965431043293886073)
        ·
          refine ⟨5256245224073282470414555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7008326965431043293886073 5256245224073282470414555)
          ·
            refine ⟨7884367836109923705621833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256245224073282470414555 7884367836109923705621833)
            ·
              refine ⟨5913275877082442779216375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7884367836109923705621833 5913275877082442779216375)
              ·
                refine ⟨8869913815623664168824563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913275877082442779216375 8869913815623664168824563)
                ·
                  refine ⟨13304870723435496253236845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869913815623664168824563 13304870723435496253236845)
                  ·
                    refine ⟨4989326521288311094963817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13304870723435496253236845 4989326521288311094963817)
                    ·
                      refine ⟨3741994890966233321222863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989326521288311094963817 3741994890966233321222863)
                      ·
                        rfl

theorem cell23_7287509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7287509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287509 prefixEnd_7287509 := by exact prefixLift 7287509
  have htrace : WordTrace (prefixWord ++ tailWord_7287509) baseStart_7287509 baseEnd_7287509 := by
    simpa [prefixWord, tailWord_7287509, baseEnd_7287509] using wordTrace_append hprefix tailTrace_7287509
  have hstable : (prefixWord ++ tailWord_7287509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287509).length < 2 ^ (prefixWord ++ tailWord_7287509).sum := by decide
  have hdescent : baseEnd_7287509 < baseStart_7287509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287511 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 5]
def baseStart_7287511 : Nat := 118140960795 + 7287511 * 2 ^ 59
def prefixEnd_7287511 : Nat := 4983230072969 + 3 ^ 40 * 7287511 * 2
def baseEnd_7287511 : Nat := 415777324214171368155317

theorem tailTrace_7287511 : CollatzResearch.WordTrace tailWord_7287511 prefixEnd_7287511 415777324214171368155317 := by
  unfold tailWord_7287511
  simp only [CollatzResearch.WordTrace]
  refine ⟨265797362301599729635622387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177198241534399819757081591 265797362301599729635622387)
  ·
    refine ⟨398696043452399594453433581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265797362301599729635622387 398696043452399594453433581)
    ·
      refine ⟨149511016294649847920037593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398696043452399594453433581 149511016294649847920037593)
      ·
        refine ⟨112133262220987385940028195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149511016294649847920037593 112133262220987385940028195)
        ·
          refine ⟨168199893331481078910042293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112133262220987385940028195 168199893331481078910042293)
          ·
            refine ⟨15768739999826351147816465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168199893331481078910042293 15768739999826351147816465)
            ·
              refine ⟨11826554999869763360862349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15768739999826351147816465 11826554999869763360862349)
              ·
                refine ⟨4434958124951161260323381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11826554999869763360862349 4434958124951161260323381)
                ·
                  refine ⟨415777324214171368155317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4434958124951161260323381 415777324214171368155317)
                  ·
                    rfl

theorem cell23_7287511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 5].length) (baseStart_7287511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287511 prefixEnd_7287511 := by exact prefixLift 7287511
  have htrace : WordTrace (prefixWord ++ tailWord_7287511) baseStart_7287511 baseEnd_7287511 := by
    simpa [prefixWord, tailWord_7287511, baseEnd_7287511] using wordTrace_append hprefix tailTrace_7287511
  have hstable : (prefixWord ++ tailWord_7287511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287511).length < 2 ^ (prefixWord ++ tailWord_7287511).sum := by decide
  have hdescent : baseEnd_7287511 < baseStart_7287511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287547 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_7287547 : Nat := 118140960795 + 7287547 * 2 ^ 59
def prefixEnd_7287547 : Nat := 4983230072969 + 3 ^ 40 * 7287547 * 2
def baseEnd_7287547 : Nat := 3742014403231104172547687

theorem tailTrace_7287547 : CollatzResearch.WordTrace tailWord_7287547 prefixEnd_7287547 3742014403231104172547687 := by
  unfold tailWord_7287547
  simp only [CollatzResearch.WordTrace]
  refine ⟨265798675329469307783932895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177199116886312871855955263 265798675329469307783932895)
  ·
    refine ⟨398698012994203961675899343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265798675329469307783932895 398698012994203961675899343)
    ·
      refine ⟨598047019491305942513849015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398698012994203961675899343 598047019491305942513849015)
      ·
        refine ⟨897070529236958913770773523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598047019491305942513849015 897070529236958913770773523)
        ·
          refine ⟨1345605793855438370656160285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897070529236958913770773523 1345605793855438370656160285)
          ·
            refine ⟨504602172695789388996060107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1345605793855438370656160285 504602172695789388996060107)
            ·
              refine ⟨756903259043684083494090161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504602172695789388996060107 756903259043684083494090161)
              ·
                refine ⟨567677444282763062620567621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756903259043684083494090161 567677444282763062620567621)
                ·
                  refine ⟨106439520803018074241356429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567677444282763062620567621 106439520803018074241356429)
                  ·
                    refine ⟨39914820301131777840508661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106439520803018074241356429 39914820301131777840508661)
                    ·
                      refine ⟨3742014403231104172547687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39914820301131777840508661 3742014403231104172547687)
                      ·
                        rfl

theorem cell23_7287547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_7287547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287547 prefixEnd_7287547 := by exact prefixLift 7287547
  have htrace : WordTrace (prefixWord ++ tailWord_7287547) baseStart_7287547 baseEnd_7287547 := by
    simpa [prefixWord, tailWord_7287547, baseEnd_7287547] using wordTrace_append hprefix tailTrace_7287547
  have hstable : (prefixWord ++ tailWord_7287547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287547).length < 2 ^ (prefixWord ++ tailWord_7287547).sum := by decide
  have hdescent : baseEnd_7287547 < baseStart_7287547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287567 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 10]
def baseStart_7287567 : Nat := 118140960795 + 7287567 * 2 ^ 59
def prefixEnd_7287567 : Nat := 4983230072969 + 3 ^ 40 * 7287567 * 2
def baseEnd_7287567 : Nat := 415780519204910454921955

theorem tailTrace_7287567 : CollatzResearch.WordTrace tailWord_7287567 prefixEnd_7287567 415780519204910454921955 := by
  unfold tailWord_7287567
  simp only [CollatzResearch.WordTrace]
  refine ⟨265799404789396851199660955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177199603192931234133107303 265799404789396851199660955)
  ·
    refine ⟨398699107184095276799491433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265799404789396851199660955 398699107184095276799491433)
    ·
      refine ⟨299024330388071457599618575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398699107184095276799491433 299024330388071457599618575)
      ·
        refine ⟨448536495582107186399427863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299024330388071457599618575 448536495582107186399427863)
        ·
          refine ⟨672804743373160779599141795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448536495582107186399427863 672804743373160779599141795)
          ·
            refine ⟨1009207115059741169398712693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672804743373160779599141795 1009207115059741169398712693)
            ·
              refine ⟨94613167036850734631129315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1009207115059741169398712693 94613167036850734631129315)
              ·
                refine ⟨141919750555276101946693973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94613167036850734631129315 141919750555276101946693973)
                ·
                  refine ⟨415780519204910454921955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141919750555276101946693973 415780519204910454921955)
                  ·
                    rfl

theorem cell23_7287567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 10].length) (baseStart_7287567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287567 prefixEnd_7287567 := by exact prefixLift 7287567
  have htrace : WordTrace (prefixWord ++ tailWord_7287567) baseStart_7287567 baseEnd_7287567 := by
    simpa [prefixWord, tailWord_7287567, baseEnd_7287567] using wordTrace_append hprefix tailTrace_7287567
  have hstable : (prefixWord ++ tailWord_7287567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287567).length < 2 ^ (prefixWord ++ tailWord_7287567).sum := by decide
  have hdescent : baseEnd_7287567 < baseStart_7287567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287584 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 8]
def baseStart_7287584 : Nat := 118140960795 + 7287584 * 2 ^ 59
def prefixEnd_7287584 : Nat := 4983230072969 + 3 ^ 40 * 7287584 * 2
def baseEnd_7287584 : Nat := 415781489112813391976113

theorem tailTrace_7287584 : CollatzResearch.WordTrace tailWord_7287584 prefixEnd_7287584 415781489112813391976113 := by
  unfold tailWord_7287584
  simp only [CollatzResearch.WordTrace]
  refine ⟨132900012415167631551514903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177200016553556842068686537 132900012415167631551514903)
  ·
    refine ⟨199350018622751447327272355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132900012415167631551514903 199350018622751447327272355)
    ·
      refine ⟨299025027934127170990908533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199350018622751447327272355 299025027934127170990908533)
      ·
        refine ⟨28033596368824422280397675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299025027934127170990908533 28033596368824422280397675)
        ·
          refine ⟨42050394553236633420596513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28033596368824422280397675 42050394553236633420596513)
          ·
            refine ⟨31537795914927475065447385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42050394553236633420596513 31537795914927475065447385)
            ·
              refine ⟨23653346936195606299085539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31537795914927475065447385 23653346936195606299085539)
              ·
                refine ⟨35480020404293409448628309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23653346936195606299085539 35480020404293409448628309)
                ·
                  refine ⟨415781489112813391976113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35480020404293409448628309 415781489112813391976113)
                  ·
                    rfl

theorem cell23_7287584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_7287584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287584 prefixEnd_7287584 := by exact prefixLift 7287584
  have htrace : WordTrace (prefixWord ++ tailWord_7287584) baseStart_7287584 baseEnd_7287584 := by
    simpa [prefixWord, tailWord_7287584, baseEnd_7287584] using wordTrace_append hprefix tailTrace_7287584
  have hstable : (prefixWord ++ tailWord_7287584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287584).length < 2 ^ (prefixWord ++ tailWord_7287584).sum := by decide
  have hdescent : baseEnd_7287584 < baseStart_7287584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287651 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 4]
def baseStart_7287651 : Nat := 118140960795 + 7287651 * 2 ^ 59
def prefixEnd_7287651 : Nat := 4983230072969 + 3 ^ 40 * 7287651 * 2
def baseEnd_7287651 : Nat := 3742067805219171765647209

theorem tailTrace_7287651 : CollatzResearch.WordTrace tailWord_7287651 prefixEnd_7287651 3742067805219171765647209 := by
  unfold tailWord_7287651
  simp only [CollatzResearch.WordTrace]
  refine ⟨265802468521092533545718807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177201645680728355697145871 265802468521092533545718807)
  ·
    refine ⟨398703702781638800318578211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265802468521092533545718807 398703702781638800318578211)
    ·
      refine ⟨598055554172458200477867317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398703702781638800318578211 598055554172458200477867317)
      ·
        refine ⟨56067708203667956294800061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 598055554172458200477867317 56067708203667956294800061)
        ·
          refine ⟨21025390576375483610550023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56067708203667956294800061 21025390576375483610550023)
          ·
            refine ⟨31538085864563225415825035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21025390576375483610550023 31538085864563225415825035)
            ·
              refine ⟨47307128796844838123737553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31538085864563225415825035 47307128796844838123737553)
              ·
                refine ⟨35480346597633628592803165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47307128796844838123737553 35480346597633628592803165)
                ·
                  refine ⟨13305129974112610722301187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35480346597633628592803165 13305129974112610722301187)
                  ·
                    refine ⟨19957694961168916083451781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13305129974112610722301187 19957694961168916083451781)
                    ·
                      refine ⟨3742067805219171765647209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19957694961168916083451781 3742067805219171765647209)
                      ·
                        rfl

theorem cell23_7287651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_7287651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287651 prefixEnd_7287651 := by exact prefixLift 7287651
  have htrace : WordTrace (prefixWord ++ tailWord_7287651) baseStart_7287651 baseEnd_7287651 := by
    simpa [prefixWord, tailWord_7287651, baseEnd_7287651] using wordTrace_append hprefix tailTrace_7287651
  have hstable : (prefixWord ++ tailWord_7287651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287651).length < 2 ^ (prefixWord ++ tailWord_7287651).sum := by decide
  have hdescent : baseEnd_7287651 < baseStart_7287651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287661 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_7287661 : Nat := 118140960795 + 7287661 * 2 ^ 59
def prefixEnd_7287661 : Nat := 4983230072969 + 3 ^ 40 * 7287661 * 2
def baseEnd_7287661 : Nat := 1247357646675238908840721

theorem tailTrace_7287661 : CollatzResearch.WordTrace tailWord_7287661 prefixEnd_7287661 1247357646675238908840721 := by
  unfold tailWord_7287661
  simp only [CollatzResearch.WordTrace]
  refine ⟨265802833251056305253582837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177201888834037536835721891 265802833251056305253582837)
  ·
    refine ⟨24919015617286528617523391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265802833251056305253582837 24919015617286528617523391)
    ·
      refine ⟨37378523425929792926285087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24919015617286528617523391 37378523425929792926285087)
      ·
        refine ⟨56067785138894689389427631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37378523425929792926285087 56067785138894689389427631)
        ·
          refine ⟨84101677708342034084141447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56067785138894689389427631 84101677708342034084141447)
          ·
            refine ⟨126152516562513051126212171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84101677708342034084141447 126152516562513051126212171)
            ·
              refine ⟨189228774843769576689318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126152516562513051126212171 189228774843769576689318257)
              ·
                refine ⟨141921581132827182516988693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189228774843769576689318257 141921581132827182516988693)
                ·
                  refine ⟨6652574115601274180483845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141921581132827182516988693 6652574115601274180483845)
                  ·
                    refine ⟨1247357646675238908840721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652574115601274180483845 1247357646675238908840721)
                    ·
                      rfl

theorem cell23_7287661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_7287661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287661 prefixEnd_7287661 := by exact prefixLift 7287661
  have htrace : WordTrace (prefixWord ++ tailWord_7287661) baseStart_7287661 baseEnd_7287661 := by
    simpa [prefixWord, tailWord_7287661, baseEnd_7287661] using wordTrace_append hprefix tailTrace_7287661
  have hstable : (prefixWord ++ tailWord_7287661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287661).length < 2 ^ (prefixWord ++ tailWord_7287661).sum := by decide
  have hdescent : baseEnd_7287661 < baseStart_7287661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287664 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_7287664 : Nat := 118140960795 + 7287664 * 2 ^ 59
def prefixEnd_7287664 : Nat := 4983230072969 + 3 ^ 40 * 7287664 * 2
def baseEnd_7287664 : Nat := 3742074480467680214784649

theorem tailTrace_7287664 : CollatzResearch.WordTrace tailWord_7287664 prefixEnd_7287664 3742074480467680214784649 := by
  unfold tailWord_7287664
  simp only [CollatzResearch.WordTrace]
  refine ⟨132901471335022718382971023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177201961780030291177294697 132901471335022718382971023)
  ·
    refine ⟨199352207002534077574456535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132901471335022718382971023 199352207002534077574456535)
    ·
      refine ⟨299028310503801116361684803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199352207002534077574456535 299028310503801116361684803)
      ·
        refine ⟨448542465755701674542527205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299028310503801116361684803 448542465755701674542527205)
        ·
          refine ⟨84101712329194063976723851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 448542465755701674542527205 84101712329194063976723851)
          ·
            refine ⟨126152568493791095965085777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84101712329194063976723851 126152568493791095965085777)
            ·
              refine ⟨94614426370343321973814333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126152568493791095965085777 94614426370343321973814333)
              ·
                refine ⟨35480409888878745740180375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94614426370343321973814333 35480409888878745740180375)
                ·
                  refine ⟨53220614833318118610270563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35480409888878745740180375 53220614833318118610270563)
                  ·
                    refine ⟨79830922249977177915405845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53220614833318118610270563 79830922249977177915405845)
                    ·
                      refine ⟨3742074480467680214784649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79830922249977177915405845 3742074480467680214784649)
                      ·
                        rfl

theorem cell23_7287664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_7287664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287664 prefixEnd_7287664 := by exact prefixLift 7287664
  have htrace : WordTrace (prefixWord ++ tailWord_7287664) baseStart_7287664 baseEnd_7287664 := by
    simpa [prefixWord, tailWord_7287664, baseEnd_7287664] using wordTrace_append hprefix tailTrace_7287664
  have hstable : (prefixWord ++ tailWord_7287664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287664).length < 2 ^ (prefixWord ++ tailWord_7287664).sum := by decide
  have hdescent : baseEnd_7287664 < baseStart_7287664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287682 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7287682 : Nat := 118140960795 + 7287682 * 2 ^ 59
def prefixEnd_7287682 : Nat := 4983230072969 + 3 ^ 40 * 7287682 * 2
def baseEnd_7287682 : Nat := 1247361241039820381453189

theorem tailTrace_7287682 : CollatzResearch.WordTrace tailWord_7287682 prefixEnd_7287682 1247361241039820381453189 := by
  unfold tailWord_7287682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66450899795995056460024325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177202399455986817226731533 66450899795995056460024325)
  ·
    refine ⟨12459543711749073086254561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66450899795995056460024325 12459543711749073086254561)
    ·
      refine ⟨9344657783811804814690921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12459543711749073086254561 9344657783811804814690921)
      ·
        refine ⟨7008493337858853611018191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9344657783811804814690921 7008493337858853611018191)
        ·
          refine ⟨10512740006788280416527287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008493337858853611018191 10512740006788280416527287)
          ·
            refine ⟨15769110010182420624790931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512740006788280416527287 15769110010182420624790931)
            ·
              refine ⟨23653665015273630937186397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15769110010182420624790931 23653665015273630937186397)
              ·
                refine ⟨8870124380727611601444899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23653665015273630937186397 8870124380727611601444899)
                ·
                  refine ⟨13305186571091417402167349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8870124380727611601444899 13305186571091417402167349)
                  ·
                    refine ⟨1247361241039820381453189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13305186571091417402167349 1247361241039820381453189)
                    ·
                      rfl

theorem cell23_7287682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7287682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287682 prefixEnd_7287682 := by exact prefixLift 7287682
  have htrace : WordTrace (prefixWord ++ tailWord_7287682) baseStart_7287682 baseEnd_7287682 := by
    simpa [prefixWord, tailWord_7287682, baseEnd_7287682] using wordTrace_append hprefix tailTrace_7287682
  have hstable : (prefixWord ++ tailWord_7287682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287682).length < 2 ^ (prefixWord ++ tailWord_7287682).sum := by decide
  have hdescent : baseEnd_7287682 < baseStart_7287682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287685 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 1, 1, 4]
def baseStart_7287685 : Nat := 118140960795 + 7287685 * 2 ^ 59
def prefixEnd_7287685 : Nat := 4983230072969 + 3 ^ 40 * 7287685 * 2
def baseEnd_7287685 : Nat := 3742085263561424632622053

theorem tailTrace_7287685 : CollatzResearch.WordTrace tailWord_7287685 prefixEnd_7287685 3742085263561424632622053 := by
  unfold tailWord_7287685
  simp only [CollatzResearch.WordTrace]
  refine ⟨265803708602969357352456509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177202472401979571568304339 265803708602969357352456509)
  ·
    refine ⟨99676390726113509007171191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265803708602969357352456509 99676390726113509007171191)
    ·
      refine ⟨149514586089170263510756787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99676390726113509007171191 149514586089170263510756787)
      ·
        refine ⟨224271879133755395266135181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149514586089170263510756787 224271879133755395266135181)
        ·
          refine ⟨84101954675158273224800693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224271879133755395266135181 84101954675158273224800693)
          ·
            refine ⟨7884558250796088114825065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84101954675158273224800693 7884558250796088114825065)
            ·
              refine ⟨5913418688097066086118799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7884558250796088114825065 5913418688097066086118799)
              ·
                refine ⟨8870128032145599129178199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913418688097066086118799 8870128032145599129178199)
                ·
                  refine ⟨13305192048218398693767299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8870128032145599129178199 13305192048218398693767299)
                  ·
                    refine ⟨19957788072327598040650949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13305192048218398693767299 19957788072327598040650949)
                    ·
                      refine ⟨3742085263561424632622053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19957788072327598040650949 3742085263561424632622053)
                      ·
                        rfl

theorem cell23_7287685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_7287685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287685 prefixEnd_7287685 := by exact prefixLift 7287685
  have htrace : WordTrace (prefixWord ++ tailWord_7287685) baseStart_7287685 baseEnd_7287685 := by
    simpa [prefixWord, tailWord_7287685, baseEnd_7287685] using wordTrace_append hprefix tailTrace_7287685
  have hstable : (prefixWord ++ tailWord_7287685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287685).length < 2 ^ (prefixWord ++ tailWord_7287685).sum := by decide
  have hdescent : baseEnd_7287685 < baseStart_7287685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287761 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_7287761 : Nat := 118140960795 + 7287761 * 2 ^ 59
def prefixEnd_7287761 : Nat := 4983230072969 + 3 ^ 40 * 7287761 * 2
def baseEnd_7287761 : Nat := 3742124288091166335271703

theorem tailTrace_7287761 : CollatzResearch.WordTrace tailWord_7287761 prefixEnd_7287761 3742124288091166335271703 := by
  unfold tailWord_7287761
  simp only [CollatzResearch.WordTrace]
  refine ⟨265806480550694022332223137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177204320367129348221482091 265806480550694022332223137)
  ·
    refine ⟨199354860413020516749167353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265806480550694022332223137 199354860413020516749167353)
    ·
      refine ⟨149516145309765387561875515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199354860413020516749167353 149516145309765387561875515)
      ·
        refine ⟨224274217964648081342813273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149516145309765387561875515 224274217964648081342813273)
        ·
          refine ⟨168205663473486061007109955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224274217964648081342813273 168205663473486061007109955)
          ·
            refine ⟨252308495210229091510664933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168205663473486061007109955 252308495210229091510664933)
            ·
              refine ⟨47307842851917954658249675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252308495210229091510664933 47307842851917954658249675)
              ·
                refine ⟨70961764277876931987374513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47307842851917954658249675 70961764277876931987374513)
                ·
                  refine ⟨53221323208407698990530885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70961764277876931987374513 53221323208407698990530885)
                  ·
                    refine ⟨9978998101576443560724541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53221323208407698990530885 9978998101576443560724541)
                    ·
                      refine ⟨3742124288091166335271703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9978998101576443560724541 3742124288091166335271703)
                      ·
                        rfl

theorem cell23_7287761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_7287761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287761 prefixEnd_7287761 := by exact prefixLift 7287761
  have htrace : WordTrace (prefixWord ++ tailWord_7287761) baseStart_7287761 baseEnd_7287761 := by
    simpa [prefixWord, tailWord_7287761, baseEnd_7287761] using wordTrace_append hprefix tailTrace_7287761
  have hstable : (prefixWord ++ tailWord_7287761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287761).length < 2 ^ (prefixWord ++ tailWord_7287761).sum := by decide
  have hdescent : baseEnd_7287761 < baseStart_7287761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287826 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7287826 : Nat := 118140960795 + 7287826 * 2 ^ 59
def prefixEnd_7287826 : Nat := 4983230072969 + 3 ^ 40 * 7287826 * 2
def baseEnd_7287826 : Nat := 3742157664333708580958905

theorem tailTrace_7287826 : CollatzResearch.WordTrace tailWord_7287826 prefixEnd_7287826 3742157664333708580958905 := by
  unfold tailWord_7287826
  simp only [CollatzResearch.WordTrace]
  refine ⟨66452212823864634608334833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177205900863639025622226221 66452212823864634608334833)
  ·
    refine ⟨49839159617898475956251125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66452212823864634608334833 49839159617898475956251125)
    ·
      refine ⟨4672421214177982120898543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49839159617898475956251125 4672421214177982120898543)
      ·
        refine ⟨7008631821266973181347815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672421214177982120898543 7008631821266973181347815)
        ·
          refine ⟨10512947731900459772021723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008631821266973181347815 10512947731900459772021723)
          ·
            refine ⟨15769421597850689658032585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512947731900459772021723 15769421597850689658032585)
            ·
              refine ⟨11827066198388017243524439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15769421597850689658032585 11827066198388017243524439)
              ·
                refine ⟨17740599297582025865286659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11827066198388017243524439 17740599297582025865286659)
                ·
                  refine ⟨26610898946373038797929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17740599297582025865286659 26610898946373038797929989)
                  ·
                    refine ⟨4989543552444944774611873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26610898946373038797929989 4989543552444944774611873)
                    ·
                      refine ⟨3742157664333708580958905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989543552444944774611873 3742157664333708580958905)
                      ·
                        rfl

theorem cell23_7287826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7287826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287826 prefixEnd_7287826 := by exact prefixLift 7287826
  have htrace : WordTrace (prefixWord ++ tailWord_7287826) baseStart_7287826 baseEnd_7287826 := by
    simpa [prefixWord, tailWord_7287826, baseEnd_7287826] using wordTrace_append hprefix tailTrace_7287826
  have hstable : (prefixWord ++ tailWord_7287826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287826).length < 2 ^ (prefixWord ++ tailWord_7287826).sum := by decide
  have hdescent : baseEnd_7287826 < baseStart_7287826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287858 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_7287858 : Nat := 118140960795 + 7287858 * 2 ^ 59
def prefixEnd_7287858 : Nat := 4983230072969 + 3 ^ 40 * 7287858 * 2
def baseEnd_7287858 : Nat := 1247391365238217485252919

theorem tailTrace_7287858 : CollatzResearch.WordTrace tailWord_7287858 prefixEnd_7287858 1247391365238217485252919 := by
  unfold tailWord_7287858
  simp only [CollatzResearch.WordTrace]
  refine ⟨66452504607835651974626057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177206678954228405265669485 66452504607835651974626057)
  ·
    refine ⟨49839378455876738980969543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66452504607835651974626057 49839378455876738980969543)
    ·
      refine ⟨74759067683815108471454315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49839378455876738980969543 74759067683815108471454315)
      ·
        refine ⟨112138601525722662707181473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74759067683815108471454315 112138601525722662707181473)
        ·
          refine ⟨84103951144291997030386105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112138601525722662707181473 84103951144291997030386105)
          ·
            refine ⟨63077963358218997772789579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84103951144291997030386105 63077963358218997772789579)
            ·
              refine ⟨94616945037328496659184369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63077963358218997772789579 94616945037328496659184369)
              ·
                refine ⟨70962708777996372494388277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94616945037328496659184369 70962708777996372494388277)
                ·
                  refine ⟨6652753947937159921348901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70962708777996372494388277 6652753947937159921348901)
                  ·
                    refine ⟨1247391365238217485252919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652753947937159921348901 1247391365238217485252919)
                    ·
                      rfl

theorem cell23_7287858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_7287858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287858 prefixEnd_7287858 := by exact prefixLift 7287858
  have htrace : WordTrace (prefixWord ++ tailWord_7287858) baseStart_7287858 baseEnd_7287858 := by
    simpa [prefixWord, tailWord_7287858, baseEnd_7287858] using wordTrace_append hprefix tailTrace_7287858
  have hstable : (prefixWord ++ tailWord_7287858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287858).length < 2 ^ (prefixWord ++ tailWord_7287858).sum := by decide
  have hdescent : baseEnd_7287858 < baseStart_7287858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287865 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7287865 : Nat := 118140960795 + 7287865 * 2 ^ 59
def prefixEnd_7287865 : Nat := 4983230072969 + 3 ^ 40 * 7287865 * 2
def baseEnd_7287865 : Nat := 3742177690079233928371225

theorem tailTrace_7287865 : CollatzResearch.WordTrace tailWord_7287865 prefixEnd_7287865 3742177690079233928371225 := by
  unfold tailWord_7287865
  simp only [CollatzResearch.WordTrace]
  refine ⟨265810273742317248094009049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177206849161544832062672699 265810273742317248094009049)
  ·
    refine ⟨199357705306737936070506787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265810273742317248094009049 199357705306737936070506787)
    ·
      refine ⟨299036557960106904105760181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199357705306737936070506787 299036557960106904105760181)
      ·
        refine ⟨28034677308760022259915017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299036557960106904105760181 28034677308760022259915017)
        ·
          refine ⟨21026007981570016694936263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28034677308760022259915017 21026007981570016694936263)
          ·
            refine ⟨31539011972355025042404395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21026007981570016694936263 31539011972355025042404395)
            ·
              refine ⟨47308517958532537563606593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31539011972355025042404395 47308517958532537563606593)
              ·
                refine ⟨35481388468899403172704945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47308517958532537563606593 35481388468899403172704945)
                ·
                  refine ⟨26611041351674552379528709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35481388468899403172704945 26611041351674552379528709)
                  ·
                    refine ⟨4989570253438978571161633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26611041351674552379528709 4989570253438978571161633)
                    ·
                      refine ⟨3742177690079233928371225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989570253438978571161633 3742177690079233928371225)
                      ·
                        rfl

theorem cell23_7287865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7287865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287865 prefixEnd_7287865 := by exact prefixLift 7287865
  have htrace : WordTrace (prefixWord ++ tailWord_7287865) baseStart_7287865 baseEnd_7287865 := by
    simpa [prefixWord, tailWord_7287865, baseEnd_7287865] using wordTrace_append hprefix tailTrace_7287865
  have hstable : (prefixWord ++ tailWord_7287865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287865).length < 2 ^ (prefixWord ++ tailWord_7287865).sum := by decide
  have hdescent : baseEnd_7287865 < baseStart_7287865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287875 : List Nat := [1, 1, 1, 3, 1, 2, 3, 6, 1, 4]
def baseStart_7287875 : Nat := 118140960795 + 7287875 * 2 ^ 59
def prefixEnd_7287875 : Nat := 4983230072969 + 3 ^ 40 * 7287875 * 2
def baseEnd_7287875 : Nat := 1247394274961926296415393

theorem tailTrace_7287875 : CollatzResearch.WordTrace tailWord_7287875 prefixEnd_7287875 1247394274961926296415393 := by
  unfold tailWord_7287875
  simp only [CollatzResearch.WordTrace]
  refine ⟨265810638472281019801873079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177207092314854013201248719 265810638472281019801873079)
  ·
    refine ⟨398715957708421529702809619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265810638472281019801873079 398715957708421529702809619)
    ·
      refine ⟨598073936562632294554214429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398715957708421529702809619 598073936562632294554214429)
      ·
        refine ⟨224277726210987110457830411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598073936562632294554214429 224277726210987110457830411)
        ·
          refine ⟨336416589316480665686745617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224277726210987110457830411 336416589316480665686745617)
          ·
            refine ⟨252312441987360499265059213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336416589316480665686745617 252312441987360499265059213)
            ·
              refine ⟨94617165745260187224397205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252312441987360499265059213 94617165745260187224397205)
              ·
                refine ⟨4435179644309071276143619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94617165745260187224397205 4435179644309071276143619)
                ·
                  refine ⟨6652769466463606914215429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435179644309071276143619 6652769466463606914215429)
                  ·
                    refine ⟨1247394274961926296415393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6652769466463606914215429 1247394274961926296415393)
                    ·
                      rfl

theorem cell23_7287875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6, 1, 4].length) (baseStart_7287875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287875 prefixEnd_7287875 := by exact prefixLift 7287875
  have htrace : WordTrace (prefixWord ++ tailWord_7287875) baseStart_7287875 baseEnd_7287875 := by
    simpa [prefixWord, tailWord_7287875, baseEnd_7287875] using wordTrace_append hprefix tailTrace_7287875
  have hstable : (prefixWord ++ tailWord_7287875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287875).length < 2 ^ (prefixWord ++ tailWord_7287875).sum := by decide
  have hdescent : baseEnd_7287875 < baseStart_7287875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287885 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_7287885 : Nat := 118140960795 + 7287885 * 2 ^ 59
def prefixEnd_7287885 : Nat := 4983230072969 + 3 ^ 40 * 7287885 * 2
def baseEnd_7287885 : Nat := 3742187959692323850121133

theorem tailTrace_7287885 : CollatzResearch.WordTrace tailWord_7287885 prefixEnd_7287885 3742187959692323850121133 := by
  unfold tailWord_7287885
  simp only [CollatzResearch.WordTrace]
  refine ⟨265811003202244791509737109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177207335468163194339824739 265811003202244791509737109)
  ·
    refine ⟨12459890775105224602018927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265811003202244791509737109 12459890775105224602018927)
    ·
      refine ⟨18689836162657836903028391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12459890775105224602018927 18689836162657836903028391)
      ·
        refine ⟨28034754243986755354542587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18689836162657836903028391 28034754243986755354542587)
        ·
          refine ⟨42052131365980133031813881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28034754243986755354542587 42052131365980133031813881)
          ·
            refine ⟨31539098524485099773860411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42052131365980133031813881 31539098524485099773860411)
            ·
              refine ⟨47308647786727649660790617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31539098524485099773860411 47308647786727649660790617)
              ·
                refine ⟨35481485840045737245592963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47308647786727649660790617 35481485840045737245592963)
                ·
                  refine ⟨53222228760068605868389445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35481485840045737245592963 53222228760068605868389445)
                  ·
                    refine ⟨9979167892512863600323021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53222228760068605868389445 9979167892512863600323021)
                    ·
                      refine ⟨3742187959692323850121133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9979167892512863600323021 3742187959692323850121133)
                      ·
                        rfl

theorem cell23_7287885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_7287885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287885 prefixEnd_7287885 := by exact prefixLift 7287885
  have htrace : WordTrace (prefixWord ++ tailWord_7287885) baseStart_7287885 baseEnd_7287885 := by
    simpa [prefixWord, tailWord_7287885, baseEnd_7287885] using wordTrace_append hprefix tailTrace_7287885
  have hstable : (prefixWord ++ tailWord_7287885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287885).length < 2 ^ (prefixWord ++ tailWord_7287885).sum := by decide
  have hdescent : baseEnd_7287885 < baseStart_7287885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7287955 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 4]
def baseStart_7287955 : Nat := 118140960795 + 7287955 * 2 ^ 59
def prefixEnd_7287955 : Nat := 4983230072969 + 3 ^ 40 * 7287955 * 2
def baseEnd_7287955 : Nat := 3742223903338138576245811

theorem tailTrace_7287955 : CollatzResearch.WordTrace tailWord_7287955 prefixEnd_7287955 3742223903338138576245811 := by
  unfold tailWord_7287955
  simp only [CollatzResearch.WordTrace]
  refine ⟨265813556311991193464785319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177209037541327462309856879 265813556311991193464785319)
  ·
    refine ⟨398720334467986790197177979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265813556311991193464785319 398720334467986790197177979)
    ·
      refine ⟨598080501701980185295766969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398720334467986790197177979 598080501701980185295766969)
      ·
        refine ⟨448560376276485138971825227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598080501701980185295766969 448560376276485138971825227)
        ·
          refine ⟨672840564414727708457737841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448560376276485138971825227 672840564414727708457737841)
          ·
            refine ⟨504630423311045781343303381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672840564414727708457737841 504630423311045781343303381)
            ·
              refine ⟨11827275546352635500233673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 504630423311045781343303381 11827275546352635500233673)
              ·
                refine ⟨8870456659764476625175255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11827275546352635500233673 8870456659764476625175255)
                ·
                  refine ⟨13305684989646714937762883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8870456659764476625175255 13305684989646714937762883)
                  ·
                    refine ⟨19958527484470072406644325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13305684989646714937762883 19958527484470072406644325)
                    ·
                      refine ⟨3742223903338138576245811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19958527484470072406644325 3742223903338138576245811)
                      ·
                        rfl

theorem cell23_7287955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_7287955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7287955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7287955 prefixEnd_7287955 := by exact prefixLift 7287955
  have htrace : WordTrace (prefixWord ++ tailWord_7287955) baseStart_7287955 baseEnd_7287955 := by
    simpa [prefixWord, tailWord_7287955, baseEnd_7287955] using wordTrace_append hprefix tailTrace_7287955
  have hstable : (prefixWord ++ tailWord_7287955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7287955).length < 2 ^ (prefixWord ++ tailWord_7287955).sum := by decide
  have hdescent : baseEnd_7287955 < baseStart_7287955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7287955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288005 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_7288005 : Nat := 118140960795 + 7288005 * 2 ^ 59
def prefixEnd_7288005 : Nat := 4983230072969 + 3 ^ 40 * 7288005 * 2
def baseEnd_7288005 : Nat := 3742249577370863380620581

theorem tailTrace_7288005 : CollatzResearch.WordTrace tailWord_7288005 prefixEnd_7288005 3742249577370863380620581 := by
  unfold tailWord_7288005
  simp only [CollatzResearch.WordTrace]
  refine ⟨265815379961810052004105469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177210253307873368002736979 265815379961810052004105469)
  ·
    refine ⟨99680767485678769501539551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265815379961810052004105469 99680767485678769501539551)
    ·
      refine ⟨149521151228518154252309327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99680767485678769501539551 149521151228518154252309327)
      ·
        refine ⟨224281726842777231378463991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149521151228518154252309327 224281726842777231378463991)
        ·
          refine ⟨336422590264165847067695987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224281726842777231378463991 336422590264165847067695987)
          ·
            refine ⟨504633885396248770601543981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336422590264165847067695987 504633885396248770601543981)
            ·
              refine ⟨189237707023593288975578993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504633885396248770601543981 189237707023593288975578993)
              ·
                refine ⟨141928280267694966731684245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189237707023593288975578993 141928280267694966731684245)
                ·
                  refine ⟨6652888137548201565547699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141928280267694966731684245 6652888137548201565547699)
                  ·
                    refine ⟨9979332206322302348321549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652888137548201565547699 9979332206322302348321549)
                    ·
                      refine ⟨3742249577370863380620581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9979332206322302348321549 3742249577370863380620581)
                      ·
                        rfl

theorem cell23_7288005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_7288005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288005 prefixEnd_7288005 := by exact prefixLift 7288005
  have htrace : WordTrace (prefixWord ++ tailWord_7288005) baseStart_7288005 baseEnd_7288005 := by
    simpa [prefixWord, tailWord_7288005, baseEnd_7288005] using wordTrace_append hprefix tailTrace_7288005
  have hstable : (prefixWord ++ tailWord_7288005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288005).length < 2 ^ (prefixWord ++ tailWord_7288005).sum := by decide
  have hdescent : baseEnd_7288005 < baseStart_7288005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288039 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7288039 : Nat := 118140960795 + 7288039 * 2 ^ 59
def prefixEnd_7288039 : Nat := 4983230072969 + 3 ^ 40 * 7288039 * 2
def baseEnd_7288039 : Nat := 3742267035713116247595425

theorem tailTrace_7288039 : CollatzResearch.WordTrace tailWord_7288039 prefixEnd_7288039 3742267035713116247595425 := by
  unfold tailWord_7288039
  simp only [CollatzResearch.WordTrace]
  refine ⟨265816620043686875810843171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177211080029124583873895447 265816620043686875810843171)
  ·
    refine ⟨398724930065530313716264757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265816620043686875810843171 398724930065530313716264757)
    ·
      refine ⟨37380462193643466910899821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 398724930065530313716264757 37380462193643466910899821)
      ·
        refine ⟨14017673322616300091587433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37380462193643466910899821 14017673322616300091587433)
        ·
          refine ⟨10513254991962225068690575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14017673322616300091587433 10513254991962225068690575)
          ·
            refine ⟨15769882487943337603035863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10513254991962225068690575 15769882487943337603035863)
            ·
              refine ⟨23654823731915006404553795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15769882487943337603035863 23654823731915006404553795)
              ·
                refine ⟨35482235597872509606830693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23654823731915006404553795 35482235597872509606830693)
                ·
                  refine ⟨6652919174601095551280755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35482235597872509606830693 6652919174601095551280755)
                  ·
                    refine ⟨9979378761901643326921133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652919174601095551280755 9979378761901643326921133)
                    ·
                      refine ⟨3742267035713116247595425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9979378761901643326921133 3742267035713116247595425)
                      ·
                        rfl

theorem cell23_7288039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7288039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288039 prefixEnd_7288039 := by exact prefixLift 7288039
  have htrace : WordTrace (prefixWord ++ tailWord_7288039) baseStart_7288039 baseEnd_7288039 := by
    simpa [prefixWord, tailWord_7288039, baseEnd_7288039] using wordTrace_append hprefix tailTrace_7288039
  have hstable : (prefixWord ++ tailWord_7288039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288039).length < 2 ^ (prefixWord ++ tailWord_7288039).sum := by decide
  have hdescent : baseEnd_7288039 < baseStart_7288039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288048 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_7288048 : Nat := 118140960795 + 7288048 * 2 ^ 59
def prefixEnd_7288048 : Nat := 4983230072969 + 3 ^ 40 * 7288048 * 2
def baseEnd_7288048 : Nat := 3742271657039006712382883

theorem tailTrace_7288048 : CollatzResearch.WordTrace tailWord_7288048 prefixEnd_7288048 3742271657039006712382883 := by
  unfold tailWord_7288048
  simp only [CollatzResearch.WordTrace]
  refine ⟨132908474150327135173960399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177211298867102846898613865 132908474150327135173960399)
  ·
    refine ⟨199362711225490702760940599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132908474150327135173960399 199362711225490702760940599)
    ·
      refine ⟨299044066838236054141410899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199362711225490702760940599 299044066838236054141410899)
      ·
        refine ⟨448566100257354081212116349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299044066838236054141410899 448566100257354081212116349)
        ·
          refine ⟨168212287596507780454543631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448566100257354081212116349 168212287596507780454543631)
          ·
            refine ⟨252318431394761670681815447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168212287596507780454543631 252318431394761670681815447)
            ·
              refine ⟨378477647092142506022723171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252318431394761670681815447 378477647092142506022723171)
              ·
                refine ⟨567716470638213759034084757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378477647092142506022723171 567716470638213759034084757)
                ·
                  refine ⟨26611709561166269954722723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 567716470638213759034084757 26611709561166269954722723)
                  ·
                    refine ⟨39917564341749404932084085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26611709561166269954722723 39917564341749404932084085)
                    ·
                      refine ⟨3742271657039006712382883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39917564341749404932084085 3742271657039006712382883)
                      ·
                        rfl

theorem cell23_7288048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_7288048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288048 prefixEnd_7288048 := by exact prefixLift 7288048
  have htrace : WordTrace (prefixWord ++ tailWord_7288048) baseStart_7288048 baseEnd_7288048 := by
    simpa [prefixWord, tailWord_7288048, baseEnd_7288048] using wordTrace_append hprefix tailTrace_7288048
  have hstable : (prefixWord ++ tailWord_7288048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288048).length < 2 ^ (prefixWord ++ tailWord_7288048).sum := by decide
  have hdescent : baseEnd_7288048 < baseStart_7288048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288113 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 2, 2, 2]
def baseStart_7288113 : Nat := 118140960795 + 7288113 * 2 ^ 59
def prefixEnd_7288113 : Nat := 4983230072969 + 3 ^ 40 * 7288113 * 2
def baseEnd_7288113 : Nat := 3742305033281548958070085

theorem tailTrace_7288113 : CollatzResearch.WordTrace tailWord_7288113 prefixEnd_7288113 3742305033281548958070085 := by
  unfold tailWord_7288113
  simp only [CollatzResearch.WordTrace]
  refine ⟨265819319045418786449036993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177212879363612524299357995 265819319045418786449036993)
  ·
    refine ⟨199364489284064089836777745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265819319045418786449036993 199364489284064089836777745)
    ·
      refine ⟨149523366963048067377583309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199364489284064089836777745 149523366963048067377583309)
      ·
        refine ⟨56071262611143025266593741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149523366963048067377583309 56071262611143025266593741)
        ·
          refine ⟨21026723479178634474972653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56071262611143025266593741 21026723479178634474972653)
          ·
            refine ⟨7885021304691987928114745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21026723479178634474972653 7885021304691987928114745)
            ·
              refine ⟨5913765978518990946086059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7885021304691987928114745 5913765978518990946086059)
              ·
                refine ⟨8870648967778486419129089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913765978518990946086059 8870648967778486419129089)
                ·
                  refine ⟨6652986725833864814346817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8870648967778486419129089 6652986725833864814346817)
                  ·
                    refine ⟨4989740044375398610760113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6652986725833864814346817 4989740044375398610760113)
                    ·
                      refine ⟨3742305033281548958070085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989740044375398610760113 3742305033281548958070085)
                      ·
                        rfl

theorem cell23_7288113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_7288113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288113 prefixEnd_7288113 := by exact prefixLift 7288113
  have htrace : WordTrace (prefixWord ++ tailWord_7288113) baseStart_7288113 baseEnd_7288113 := by
    simpa [prefixWord, tailWord_7288113, baseEnd_7288113] using wordTrace_append hprefix tailTrace_7288113
  have hstable : (prefixWord ++ tailWord_7288113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288113).length < 2 ^ (prefixWord ++ tailWord_7288113).sum := by decide
  have hdescent : baseEnd_7288113 < baseStart_7288113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288152 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 2, 4, 2]
def baseStart_7288152 : Nat := 118140960795 + 7288152 * 2 ^ 59
def prefixEnd_7288152 : Nat := 4983230072969 + 3 ^ 40 * 7288152 * 2
def baseEnd_7288152 : Nat := 3742325059027074305482405

theorem tailTrace_7288152 : CollatzResearch.WordTrace tailWord_7288152 prefixEnd_7288152 3742325059027074305482405 := by
  unfold tailWord_7288152
  simp only [CollatzResearch.WordTrace]
  refine ⟨132910370746138748054853355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177213827661518330739804473 132910370746138748054853355)
  ·
    refine ⟨199365556119208122082280033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132910370746138748054853355 199365556119208122082280033)
    ·
      refine ⟨149524167089406091561710025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199365556119208122082280033 149524167089406091561710025)
      ·
        refine ⟨112143125317054568671282519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149524167089406091561710025 112143125317054568671282519)
        ·
          refine ⟨168214687975581853006923779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112143125317054568671282519 168214687975581853006923779)
          ·
            refine ⟨252322031963372779510385669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168214687975581853006923779 252322031963372779510385669)
            ·
              refine ⟨47310380993132396158197313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252322031963372779510385669 47310380993132396158197313)
              ·
                refine ⟨35482785744849297118647985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47310380993132396158197313 35482785744849297118647985)
                ·
                  refine ⟨26612089308636972838985989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35482785744849297118647985 26612089308636972838985989)
                  ·
                    refine ⟨4989766745369432407309873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26612089308636972838985989 4989766745369432407309873)
                    ·
                      refine ⟨3742325059027074305482405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989766745369432407309873 3742325059027074305482405)
                      ·
                        rfl

theorem cell23_7288152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_7288152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288152 prefixEnd_7288152 := by exact prefixLift 7288152
  have htrace : WordTrace (prefixWord ++ tailWord_7288152) baseStart_7288152 baseEnd_7288152 := by
    simpa [prefixWord, tailWord_7288152, baseEnd_7288152] using wordTrace_append hprefix tailTrace_7288152
  have hstable : (prefixWord ++ tailWord_7288152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288152).length < 2 ^ (prefixWord ++ tailWord_7288152).sum := by decide
  have hdescent : baseEnd_7288152 < baseStart_7288152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288175 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 6]
def baseStart_7288175 : Nat := 118140960795 + 7288175 * 2 ^ 59
def prefixEnd_7288175 : Nat := 4983230072969 + 3 ^ 40 * 7288175 * 2
def baseEnd_7288175 : Nat := 415815207675791968388311

theorem tailTrace_7288175 : CollatzResearch.WordTrace tailWord_7288175 prefixEnd_7288175 415815207675791968388311 := by
  unfold tailWord_7288175
  simp only [CollatzResearch.WordTrace]
  refine ⟨265821580371194171037793979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177214386914129447358529319 265821580371194171037793979)
  ·
    refine ⟨398732370556791256556690969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265821580371194171037793979 398732370556791256556690969)
    ·
      refine ⟨299049277917593442417518227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398732370556791256556690969 299049277917593442417518227)
      ·
        refine ⟨448573916876390163626277341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299049277917593442417518227 448573916876390163626277341)
        ·
          refine ⟨168215218828646311359854003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448573916876390163626277341 168215218828646311359854003)
          ·
            refine ⟨252322828242969467039781005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168215218828646311359854003 252322828242969467039781005)
            ·
              refine ⟨94621060591113550139917877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252322828242969467039781005 94621060591113550139917877)
              ·
                refine ⟨8870724430416895325617301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94621060591113550139917877 8870724430416895325617301)
                ·
                  refine ⟨415815207675791968388311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8870724430416895325617301 415815207675791968388311)
                  ·
                    rfl

theorem cell23_7288175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 6].length) (baseStart_7288175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288175 prefixEnd_7288175 := by exact prefixLift 7288175
  have htrace : WordTrace (prefixWord ++ tailWord_7288175) baseStart_7288175 baseEnd_7288175 := by
    simpa [prefixWord, tailWord_7288175, baseEnd_7288175] using wordTrace_append hprefix tailTrace_7288175
  have hstable : (prefixWord ++ tailWord_7288175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288175).length < 2 ^ (prefixWord ++ tailWord_7288175).sum := by decide
  have hdescent : baseEnd_7288175 < baseStart_7288175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288196 : List Nat := [2, 3, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_7288196 : Nat := 118140960795 + 7288196 * 2 ^ 59
def prefixEnd_7288196 : Nat := 4983230072969 + 3 ^ 40 * 7288196 * 2
def baseEnd_7288196 : Nat := 1247449217391957377777401

theorem tailTrace_7288196 : CollatzResearch.WordTrace tailWord_7288196 prefixEnd_7288196 1247449217391957377777401 := by
  unfold tailWord_7288196
  simp only [CollatzResearch.WordTrace]
  refine ⟨132911173152059045812154221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177214897536078727749538961 132911173152059045812154221)
  ·
    refine ⟨49841689932022142179557833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132911173152059045812154221 49841689932022142179557833)
    ·
      refine ⟨37381267449016606634668375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49841689932022142179557833 37381267449016606634668375)
      ·
        refine ⟨56071901173524909952002563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37381267449016606634668375 56071901173524909952002563)
        ·
          refine ⟨84107851760287364928003845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56071901173524909952002563 84107851760287364928003845)
          ·
            refine ⟨15770222205053880924000721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84107851760287364928003845 15770222205053880924000721)
            ·
              refine ⟨11827666653790410693000541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15770222205053880924000721 11827666653790410693000541)
              ·
                refine ⟨4435374995171404009875203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11827666653790410693000541 4435374995171404009875203)
                ·
                  refine ⟨6653062492757106014812805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435374995171404009875203 6653062492757106014812805)
                  ·
                    refine ⟨1247449217391957377777401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6653062492757106014812805 1247449217391957377777401)
                    ·
                      rfl

theorem cell23_7288196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_7288196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288196 prefixEnd_7288196 := by exact prefixLift 7288196
  have htrace : WordTrace (prefixWord ++ tailWord_7288196) baseStart_7288196 baseEnd_7288196 := by
    simpa [prefixWord, tailWord_7288196, baseEnd_7288196] using wordTrace_append hprefix tailTrace_7288196
  have hstable : (prefixWord ++ tailWord_7288196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288196).length < 2 ^ (prefixWord ++ tailWord_7288196).sum := by decide
  have hdescent : baseEnd_7288196 < baseStart_7288196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288212 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7288212 : Nat := 118140960795 + 7288212 * 2 ^ 59
def prefixEnd_7288212 : Nat := 4983230072969 + 3 ^ 40 * 7288212 * 2
def baseEnd_7288212 : Nat := 3742355867866344070732129

theorem tailTrace_7288212 : CollatzResearch.WordTrace tailWord_7288212 prefixEnd_7288212 3742355867866344070732129 := by
  unfold tailWord_7288212
  simp only [CollatzResearch.WordTrace]
  refine ⟨132911464936030063178445445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177215286581373417571260593 132911464936030063178445445)
  ·
    refine ⟨24920899675505636845958521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132911464936030063178445445 24920899675505636845958521)
    ·
      refine ⟨18690674756629227634468891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24920899675505636845958521 18690674756629227634468891)
      ·
        refine ⟨28036012134943841451703337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18690674756629227634468891 28036012134943841451703337)
        ·
          refine ⟨21027009101207881088777503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28036012134943841451703337 21027009101207881088777503)
          ·
            refine ⟨31540513651811821633166255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21027009101207881088777503 31540513651811821633166255)
            ·
              refine ⟨47310770477717732449749383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31540513651811821633166255 47310770477717732449749383)
              ·
                refine ⟨70966155716576598674624075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47310770477717732449749383 70966155716576598674624075)
                ·
                  refine ⟨106449233574864898011936113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70966155716576598674624075 106449233574864898011936113)
                  ·
                    refine ⟨79836925181148673508952085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106449233574864898011936113 79836925181148673508952085)
                    ·
                      refine ⟨3742355867866344070732129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79836925181148673508952085 3742355867866344070732129)
                      ·
                        rfl

theorem cell23_7288212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7288212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288212 prefixEnd_7288212 := by exact prefixLift 7288212
  have htrace : WordTrace (prefixWord ++ tailWord_7288212) baseStart_7288212 baseEnd_7288212 := by
    simpa [prefixWord, tailWord_7288212, baseEnd_7288212] using wordTrace_append hprefix tailTrace_7288212
  have hstable : (prefixWord ++ tailWord_7288212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288212).length < 2 ^ (prefixWord ++ tailWord_7288212).sum := by decide
  have hdescent : baseEnd_7288212 < baseStart_7288212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288259 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 5, 2, 2]
def baseStart_7288259 : Nat := 118140960795 + 7288259 * 2 ^ 59
def prefixEnd_7288259 : Nat := 4983230072969 + 3 ^ 40 * 7288259 * 2
def baseEnd_7288259 : Nat := 3742380001457105386844413

theorem tailTrace_7288259 : CollatzResearch.WordTrace tailWord_7288259 prefixEnd_7288259 3742380001457105386844413 := by
  unfold tailWord_7288259
  simp only [CollatzResearch.WordTrace]
  refine ⟨265824644102889853383851831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177216429401926568922567887 265824644102889853383851831)
  ·
    refine ⟨398736966154334780075777747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265824644102889853383851831 398736966154334780075777747)
    ·
      refine ⟨598105449231502170113666621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398736966154334780075777747 598105449231502170113666621)
      ·
        refine ⟨224289543461813313792624983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598105449231502170113666621 224289543461813313792624983)
        ·
          refine ⟨336434315192719970688937475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224289543461813313792624983 336434315192719970688937475)
          ·
            refine ⟨504651472789079956033406213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336434315192719970688937475 504651472789079956033406213)
            ·
              refine ⟨94622151147952491756263665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 504651472789079956033406213 94622151147952491756263665)
              ·
                refine ⟨70966613360964368817197749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94622151147952491756263665 70966613360964368817197749)
                ·
                  refine ⟨6653120002590409576612289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70966613360964368817197749 6653120002590409576612289)
                  ·
                    refine ⟨4989840001942807182459217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653120002590409576612289 4989840001942807182459217)
                    ·
                      refine ⟨3742380001457105386844413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989840001942807182459217 3742380001457105386844413)
                      ·
                        rfl

theorem cell23_7288259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_7288259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288259 prefixEnd_7288259 := by exact prefixLift 7288259
  have htrace : WordTrace (prefixWord ++ tailWord_7288259) baseStart_7288259 baseEnd_7288259 := by
    simpa [prefixWord, tailWord_7288259, baseEnd_7288259] using wordTrace_append hprefix tailTrace_7288259
  have hstable : (prefixWord ++ tailWord_7288259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288259).length < 2 ^ (prefixWord ++ tailWord_7288259).sum := by decide
  have hdescent : baseEnd_7288259 < baseStart_7288259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288282 : List Nat := [3, 1, 1, 2, 3, 3, 2, 8]
def baseStart_7288282 : Nat := 118140960795 + 7288282 * 2 ^ 59
def prefixEnd_7288282 : Nat := 4983230072969 + 3 ^ 40 * 7288282 * 2
def baseEnd_7288282 : Nat := 138607104130079955439141

theorem tailTrace_7288282 : CollatzResearch.WordTrace tailWord_7288282 prefixEnd_7288282 138607104130079955439141 := by
  unfold tailWord_7288282
  simp only [CollatzResearch.WordTrace]
  refine ⟨66456370745451632077984775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177216988654537685541292733 66456370745451632077984775)
  ·
    refine ⟨99684556118177448116977163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66456370745451632077984775 99684556118177448116977163)
    ·
      refine ⟨149526834177266172175465745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99684556118177448116977163 149526834177266172175465745)
      ·
        refine ⟨112145125632949629131599309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149526834177266172175465745 112145125632949629131599309)
        ·
          refine ⟨42054422112356110924349741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112145125632949629131599309 42054422112356110924349741)
          ·
            refine ⟨15770408292133541596631153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42054422112356110924349741 15770408292133541596631153)
            ·
              refine ⟨11827806219100156197473365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15770408292133541596631153 11827806219100156197473365)
              ·
                refine ⟨138607104130079955439141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11827806219100156197473365 138607104130079955439141)
                ·
                  rfl

theorem cell23_7288282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_7288282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288282 prefixEnd_7288282 := by exact prefixLift 7288282
  have htrace : WordTrace (prefixWord ++ tailWord_7288282) baseStart_7288282 baseEnd_7288282 := by
    simpa [prefixWord, tailWord_7288282, baseEnd_7288282] using wordTrace_append hprefix tailTrace_7288282
  have hstable : (prefixWord ++ tailWord_7288282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288282).length < 2 ^ (prefixWord ++ tailWord_7288282).sum := by decide
  have hdescent : baseEnd_7288282 < baseStart_7288282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288292 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_7288292 : Nat := 118140960795 + 7288292 * 2 ^ 59
def prefixEnd_7288292 : Nat := 4983230072969 + 3 ^ 40 * 7288292 * 2
def baseEnd_7288292 : Nat := 3742396946318703757731761

theorem tailTrace_7288292 : CollatzResearch.WordTrace tailWord_7288292 prefixEnd_7288292 3742396946318703757731761 := by
  unfold tailWord_7288292
  simp only [CollatzResearch.WordTrace]
  refine ⟨132912923855885150009901565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177217231807846866679868753 132912923855885150009901565)
  ·
    refine ⟨49842346445956931253713087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132912923855885150009901565 49842346445956931253713087)
    ·
      refine ⟨74763519668935396880569631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49842346445956931253713087 74763519668935396880569631)
      ·
        refine ⟨112145279503403095320854447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74763519668935396880569631 112145279503403095320854447)
        ·
          refine ⟨168217919255104642981281671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112145279503403095320854447 168217919255104642981281671)
          ·
            refine ⟨252326878882656964471922507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168217919255104642981281671 252326878882656964471922507)
            ·
              refine ⟨378490318323985446707883761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252326878882656964471922507 378490318323985446707883761)
              ·
                refine ⟨283867738742989085030912821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378490318323985446707883761 283867738742989085030912821)
                ·
                  refine ⟨26612600507155226721648077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283867738742989085030912821 26612600507155226721648077)
                  ·
                    refine ⟨9979725190183210020618029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26612600507155226721648077 9979725190183210020618029)
                    ·
                      refine ⟨3742396946318703757731761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9979725190183210020618029 3742396946318703757731761)
                      ·
                        rfl

theorem cell23_7288292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_7288292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288292 prefixEnd_7288292 := by exact prefixLift 7288292
  have htrace : WordTrace (prefixWord ++ tailWord_7288292) baseStart_7288292 baseEnd_7288292 := by
    simpa [prefixWord, tailWord_7288292, baseEnd_7288292] using wordTrace_append hprefix tailTrace_7288292
  have hstable : (prefixWord ++ tailWord_7288292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288292).length < 2 ^ (prefixWord ++ tailWord_7288292).sum := by decide
  have hdescent : baseEnd_7288292 < baseStart_7288292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288315 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_7288315 : Nat := 118140960795 + 7288315 * 2 ^ 59
def prefixEnd_7288315 : Nat := 4983230072969 + 3 ^ 40 * 7288315 * 2
def baseEnd_7288315 : Nat := 3742408756373757167744155

theorem tailTrace_7288315 : CollatzResearch.WordTrace tailWord_7288315 prefixEnd_7288315 3742408756373757167744155 := by
  unfold tailWord_7288315
  simp only [CollatzResearch.WordTrace]
  refine ⟨265826686590686974947890399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177217791060457983298593599 265826686590686974947890399)
  ·
    refine ⟨398740029886030462421835599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265826686590686974947890399 398740029886030462421835599)
    ·
      refine ⟨598110044829045693632753399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398740029886030462421835599 598110044829045693632753399)
      ·
        refine ⟨897165067243568540449130099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598110044829045693632753399 897165067243568540449130099)
        ·
          refine ⟨1345747600865352810673695149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897165067243568540449130099 1345747600865352810673695149)
          ·
            refine ⟨504655350324507304002635681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1345747600865352810673695149 504655350324507304002635681)
            ·
              refine ⟨378491512743380478001976761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504655350324507304002635681 378491512743380478001976761)
              ·
                refine ⟨283868634557535358501482571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378491512743380478001976761 283868634557535358501482571)
                ·
                  refine ⟨425802951836303037752223857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283868634557535358501482571 425802951836303037752223857)
                  ·
                    refine ⟨319352213877227278314167893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 425802951836303037752223857 319352213877227278314167893)
                    ·
                      refine ⟨3742408756373757167744155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 319352213877227278314167893 3742408756373757167744155)
                      ·
                        rfl

theorem cell23_7288315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_7288315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288315 prefixEnd_7288315 := by exact prefixLift 7288315
  have htrace : WordTrace (prefixWord ++ tailWord_7288315) baseStart_7288315 baseEnd_7288315 := by
    simpa [prefixWord, tailWord_7288315, baseEnd_7288315] using wordTrace_append hprefix tailTrace_7288315
  have hstable : (prefixWord ++ tailWord_7288315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288315).length < 2 ^ (prefixWord ++ tailWord_7288315).sum := by decide
  have hdescent : baseEnd_7288315 < baseStart_7288315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288327 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_7288327 : Nat := 118140960795 + 7288327 * 2 ^ 59
def prefixEnd_7288327 : Nat := 4983230072969 + 3 ^ 40 * 7288327 * 2
def baseEnd_7288327 : Nat := 3742414918141611120794101

theorem tailTrace_7288327 : CollatzResearch.WordTrace tailWord_7288327 prefixEnd_7288327 3742414918141611120794101 := by
  unfold tailWord_7288327
  simp only [CollatzResearch.WordTrace]
  refine ⟨265827124266643500997327235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177218082844429000664884823 265827124266643500997327235)
  ·
    refine ⟨398740686399965251495990853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265827124266643500997327235 398740686399965251495990853)
    ·
      refine ⟨74763878699993484655498285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398740686399965251495990853 74763878699993484655498285)
      ·
        refine ⟨28036454512497556745811857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74763878699993484655498285 28036454512497556745811857)
        ·
          refine ⟨21027340884373167559358893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28036454512497556745811857 21027340884373167559358893)
          ·
            refine ⟨7885252831639937834759585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21027340884373167559358893 7885252831639937834759585)
            ·
              refine ⟨5913939623729953376069689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7885252831639937834759585 5913939623729953376069689)
              ·
                refine ⟨4435454717797465032052267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5913939623729953376069689 4435454717797465032052267)
                ·
                  refine ⟨6653182076696197548078401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435454717797465032052267 6653182076696197548078401)
                  ·
                    refine ⟨4989886557522148161058801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653182076696197548078401 4989886557522148161058801)
                    ·
                      refine ⟨3742414918141611120794101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989886557522148161058801 3742414918141611120794101)
                      ·
                        rfl

theorem cell23_7288327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_7288327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288327 prefixEnd_7288327 := by exact prefixLift 7288327
  have htrace : WordTrace (prefixWord ++ tailWord_7288327) baseStart_7288327 baseEnd_7288327 := by
    simpa [prefixWord, tailWord_7288327, baseEnd_7288327] using wordTrace_append hprefix tailTrace_7288327
  have hstable : (prefixWord ++ tailWord_7288327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288327).length < 2 ^ (prefixWord ++ tailWord_7288327).sum := by decide
  have hdescent : baseEnd_7288327 < baseStart_7288327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288333 : List Nat := [1, 7, 1, 1, 2, 2, 1, 8]
def baseStart_7288333 : Nat := 118140960795 + 7288333 * 2 ^ 59
def prefixEnd_7288333 : Nat := 4983230072969 + 3 ^ 40 * 7288333 * 2
def baseEnd_7288333 : Nat := 138608074037982892493299

theorem tailTrace_7288333 : CollatzResearch.WordTrace tailWord_7288333 prefixEnd_7288333 138608074037982892493299 := by
  unfold tailWord_7288333
  simp only [CollatzResearch.WordTrace]
  refine ⟨265827343104621764022045653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177218228736414509348030435 265827343104621764022045653)
  ·
    refine ⟨6230328354014572594266695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 265827343104621764022045653 6230328354014572594266695)
    ·
      refine ⟨9345492531021858891400043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6230328354014572594266695 9345492531021858891400043)
      ·
        refine ⟨14018238796532788337100065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9345492531021858891400043 14018238796532788337100065)
        ·
          refine ⟨10513679097399591252825049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14018238796532788337100065 10513679097399591252825049)
          ·
            refine ⟨7885259323049693439618787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10513679097399591252825049 7885259323049693439618787)
            ·
              refine ⟨11827888984574540159428181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885259323049693439618787 11827888984574540159428181)
              ·
                refine ⟨138608074037982892493299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11827888984574540159428181 138608074037982892493299)
                ·
                  rfl

theorem cell23_7288333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 8].length) (baseStart_7288333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288333 prefixEnd_7288333 := by exact prefixLift 7288333
  have htrace : WordTrace (prefixWord ++ tailWord_7288333) baseStart_7288333 baseEnd_7288333 := by
    simpa [prefixWord, tailWord_7288333, baseEnd_7288333] using wordTrace_append hprefix tailTrace_7288333
  have hstable : (prefixWord ++ tailWord_7288333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288333).length < 2 ^ (prefixWord ++ tailWord_7288333).sum := by decide
  have hdescent : baseEnd_7288333 < baseStart_7288333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288350 : List Nat := [4, 3, 3, 1, 1, 1, 3, 7]
def baseStart_7288350 : Nat := 118140960795 + 7288350 * 2 ^ 59
def prefixEnd_7288350 : Nat := 4983230072969 + 3 ^ 40 * 7288350 * 2
def baseEnd_7288350 : Nat := 138608397340617204844685

theorem tailTrace_7288350 : CollatzResearch.WordTrace tailWord_7288350 prefixEnd_7288350 138608397340617204844685 := by
  unfold tailWord_7288350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33228495393195021990676813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177218642097040117283609669 33228495393195021990676813)
  ·
    refine ⟨12460685772448133246503805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33228495393195021990676813 12460685772448133246503805)
    ·
      refine ⟨4672757164668049967438927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12460685772448133246503805 4672757164668049967438927)
      ·
        refine ⟨7009135747002074951158391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672757164668049967438927 7009135747002074951158391)
        ·
          refine ⟨10513703620503112426737587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7009135747002074951158391 10513703620503112426737587)
          ·
            refine ⟨15770555430754668640106381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10513703620503112426737587 15770555430754668640106381)
            ·
              refine ⟨5913958286533000740039893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15770555430754668640106381 5913958286533000740039893)
              ·
                refine ⟨138608397340617204844685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5913958286533000740039893 138608397340617204844685)
                ·
                  rfl

theorem cell23_7288350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_7288350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288350 prefixEnd_7288350 := by exact prefixLift 7288350
  have htrace : WordTrace (prefixWord ++ tailWord_7288350) baseStart_7288350 baseEnd_7288350 := by
    simpa [prefixWord, tailWord_7288350, baseEnd_7288350] using wordTrace_append hprefix tailTrace_7288350
  have hstable : (prefixWord ++ tailWord_7288350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288350).length < 2 ^ (prefixWord ++ tailWord_7288350).sum := by decide
  have hdescent : baseEnd_7288350 < baseStart_7288350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288383 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 2, 2, 2]
def baseStart_7288383 : Nat := 118140960795 + 7288383 * 2 ^ 59
def prefixEnd_7288383 : Nat := 4983230072969 + 3 ^ 40 * 7288383 * 2
def baseEnd_7288383 : Nat := 3742443673058262901693843

theorem tailTrace_7288383 : CollatzResearch.WordTrace tailWord_7288383 prefixEnd_7288383 3742443673058262901693843 := by
  unfold tailWord_7288383
  simp only [CollatzResearch.WordTrace]
  refine ⟨265829166754440622561365803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177219444502960415040910535 265829166754440622561365803)
  ·
    refine ⟨398743750131660933842048705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265829166754440622561365803 398743750131660933842048705)
    ·
      refine ⟨299057812598745700381536529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398743750131660933842048705 299057812598745700381536529)
      ·
        refine ⟨224293359449059275286152397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299057812598745700381536529 224293359449059275286152397)
        ·
          refine ⟨84110009793397228232307149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224293359449059275286152397 84110009793397228232307149)
          ·
            refine ⟨31541253672523960587115181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84110009793397228232307149 31541253672523960587115181)
            ·
              refine ⟨11827970127196485220168193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31541253672523960587115181 11827970127196485220168193)
              ·
                refine ⟨8870977595397363915126145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11827970127196485220168193 8870977595397363915126145)
                ·
                  refine ⟨6653233196548022936344609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8870977595397363915126145 6653233196548022936344609)
                  ·
                    refine ⟨4989924897411017202258457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653233196548022936344609 4989924897411017202258457)
                    ·
                      refine ⟨3742443673058262901693843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989924897411017202258457 3742443673058262901693843)
                      ·
                        rfl

theorem cell23_7288383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_7288383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288383 prefixEnd_7288383 := by exact prefixLift 7288383
  have htrace : WordTrace (prefixWord ++ tailWord_7288383) baseStart_7288383 baseEnd_7288383 := by
    simpa [prefixWord, tailWord_7288383, baseEnd_7288383] using wordTrace_append hprefix tailTrace_7288383
  have hstable : (prefixWord ++ tailWord_7288383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288383).length < 2 ^ (prefixWord ++ tailWord_7288383).sum := by decide
  have hdescent : baseEnd_7288383 < baseStart_7288383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288389 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 5]
def baseStart_7288389 : Nat := 118140960795 + 7288389 * 2 ^ 59
def prefixEnd_7288389 : Nat := 4983230072969 + 3 ^ 40 * 7288389 * 2
def baseEnd_7288389 : Nat := 415827417104687764246535

theorem tailTrace_7288389 : CollatzResearch.WordTrace tailWord_7288389 prefixEnd_7288389 415827417104687764246535 := by
  unfold tailWord_7288389
  simp only [CollatzResearch.WordTrace]
  refine ⟨265829385592418885586084221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177219590394945923724056147 265829385592418885586084221)
  ·
    refine ⟨99686019597157082094781583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265829385592418885586084221 99686019597157082094781583)
    ·
      refine ⟨149529029395735623142172375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99686019597157082094781583 149529029395735623142172375)
      ·
        refine ⟨224293544093603434713258563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149529029395735623142172375 224293544093603434713258563)
        ·
          refine ⟨336440316140405152069887845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224293544093603434713258563 336440316140405152069887845)
          ·
            refine ⟨63082559276325966013103971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336440316140405152069887845 63082559276325966013103971)
            ·
              refine ⟨94623838914488949019655957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63082559276325966013103971 94623838914488949019655957)
              ·
                refine ⟨4435492449116669485296373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94623838914488949019655957 4435492449116669485296373)
                ·
                  refine ⟨415827417104687764246535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4435492449116669485296373 415827417104687764246535)
                  ·
                    rfl

theorem cell23_7288389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_7288389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288389 prefixEnd_7288389 := by exact prefixLift 7288389
  have htrace : WordTrace (prefixWord ++ tailWord_7288389) baseStart_7288389 baseEnd_7288389 := by
    simpa [prefixWord, tailWord_7288389, baseEnd_7288389] using wordTrace_append hprefix tailTrace_7288389
  have hstable : (prefixWord ++ tailWord_7288389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288389).length < 2 ^ (prefixWord ++ tailWord_7288389).sum := by decide
  have hdescent : baseEnd_7288389 < baseStart_7288389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288409 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 2, 5, 2]
def baseStart_7288409 : Nat := 118140960795 + 7288409 * 2 ^ 59
def prefixEnd_7288409 : Nat := 4983230072969 + 3 ^ 40 * 7288409 * 2
def baseEnd_7288409 : Nat := 3742457023555279799968723

theorem tailTrace_7288409 : CollatzResearch.WordTrace tailWord_7288409 prefixEnd_7288409 3742457023555279799968723 := by
  unfold tailWord_7288409
  simp only [CollatzResearch.WordTrace]
  refine ⟨265830115052346429001812281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177220076701564286001208187 265830115052346429001812281)
  ·
    refine ⟨199372586289259821751359211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265830115052346429001812281 199372586289259821751359211)
    ·
      refine ⟨299058879433889732627038817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199372586289259821751359211 299058879433889732627038817)
      ·
        refine ⟨224294159575417299470279113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299058879433889732627038817 224294159575417299470279113)
        ·
          refine ⟨168220619681562974602709335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224294159575417299470279113 168220619681562974602709335)
          ·
            refine ⟨252330929522344461904064003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168220619681562974602709335 252330929522344461904064003)
            ·
              refine ⟨378496394283516692856096005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252330929522344461904064003 378496394283516692856096005)
              ·
                refine ⟨70968073928159379910518001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378496394283516692856096005 70968073928159379910518001)
                ·
                  refine ⟨53226055446119534932888501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70968073928159379910518001 53226055446119534932888501)
                  ·
                    refine ⟨4989942698073706399958297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53226055446119534932888501 4989942698073706399958297)
                    ·
                      refine ⟨3742457023555279799968723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4989942698073706399958297 3742457023555279799968723)
                      ·
                        rfl

theorem cell23_7288409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_7288409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288409 prefixEnd_7288409 := by exact prefixLift 7288409
  have htrace : WordTrace (prefixWord ++ tailWord_7288409) baseStart_7288409 baseEnd_7288409 := by
    simpa [prefixWord, tailWord_7288409, baseEnd_7288409] using wordTrace_append hprefix tailTrace_7288409
  have hstable : (prefixWord ++ tailWord_7288409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288409).length < 2 ^ (prefixWord ++ tailWord_7288409).sum := by decide
  have hdescent : baseEnd_7288409 < baseStart_7288409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288442 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_7288442 : Nat := 118140960795 + 7288442 * 2 ^ 59
def prefixEnd_7288442 : Nat := 4983230072969 + 3 ^ 40 * 7288442 * 2
def baseEnd_7288442 : Nat := 3742473968416878170856071

theorem tailTrace_7288442 : CollatzResearch.WordTrace tailWord_7288442 prefixEnd_7288442 3742473968416878170856071 := by
  unfold tailWord_7288442
  simp only [CollatzResearch.WordTrace]
  refine ⟨66457829665306718909440895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177220879107484583758509053 66457829665306718909440895)
  ·
    refine ⟨99686744497960078364161343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66457829665306718909440895 99686744497960078364161343)
    ·
      refine ⟨149530116746940117546242015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99686744497960078364161343 149530116746940117546242015)
      ·
        refine ⟨224295175120410176319363023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149530116746940117546242015 224295175120410176319363023)
        ·
          refine ⟨336442762680615264479044535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224295175120410176319363023 336442762680615264479044535)
          ·
            refine ⟨504664144020922896718566803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336442762680615264479044535 504664144020922896718566803)
            ·
              refine ⟨756996216031384345077850205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504664144020922896718566803 756996216031384345077850205)
              ·
                refine ⟨283873581011769129404193827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756996216031384345077850205 283873581011769129404193827)
                ·
                  refine ⟨425810371517653694106290741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283873581011769129404193827 425810371517653694106290741)
                  ·
                    refine ⟨39919722329780033822464757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 425810371517653694106290741 39919722329780033822464757)
                    ·
                      refine ⟨3742473968416878170856071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39919722329780033822464757 3742473968416878170856071)
                      ·
                        rfl

theorem cell23_7288442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_7288442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288442 prefixEnd_7288442 := by exact prefixLift 7288442
  have htrace : WordTrace (prefixWord ++ tailWord_7288442) baseStart_7288442 baseEnd_7288442 := by
    simpa [prefixWord, tailWord_7288442, baseEnd_7288442] using wordTrace_append hprefix tailTrace_7288442
  have hstable : (prefixWord ++ tailWord_7288442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288442).length < 2 ^ (prefixWord ++ tailWord_7288442).sum := by decide
  have hdescent : baseEnd_7288442 < baseStart_7288442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288459 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 3]
def baseStart_7288459 : Nat := 118140960795 + 7288459 * 2 ^ 59
def prefixEnd_7288459 : Nat := 4983230072969 + 3 ^ 40 * 7288459 * 2
def baseEnd_7288459 : Nat := 3742482697588004604343493

theorem tailTrace_7288459 : CollatzResearch.WordTrace tailWord_7288459 prefixEnd_7288459 3742482697588004604343493 := by
  unfold tailWord_7288459
  simp only [CollatzResearch.WordTrace]
  refine ⟨265831938702165287541132431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177221292468110191694088287 265831938702165287541132431)
  ·
    refine ⟨398747908053247931311698647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265831938702165287541132431 398747908053247931311698647)
    ·
      refine ⟨598121862079871896967547971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398747908053247931311698647 598121862079871896967547971)
      ·
        refine ⟨897182793119807845451321957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598121862079871896967547971 897182793119807845451321957)
        ·
          refine ⟨168221773709963971022122867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 897182793119807845451321957 168221773709963971022122867)
          ·
            refine ⟨252332660564945956533184301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168221773709963971022122867 252332660564945956533184301)
            ·
              refine ⟨94624747711854733699944113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252332660564945956533184301 94624747711854733699944113)
              ·
                refine ⟨70968560783891050274958085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94624747711854733699944113 70968560783891050274958085)
                ·
                  refine ⟨13306605146979571926554641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70968560783891050274958085 13306605146979571926554641)
                  ·
                    refine ⟨9979953860234678944915981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13306605146979571926554641 9979953860234678944915981)
                    ·
                      refine ⟨3742482697588004604343493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9979953860234678944915981 3742482697588004604343493)
                      ·
                        rfl

theorem cell23_7288459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 3].length) (baseStart_7288459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288459 prefixEnd_7288459 := by exact prefixLift 7288459
  have htrace : WordTrace (prefixWord ++ tailWord_7288459) baseStart_7288459 baseEnd_7288459 := by
    simpa [prefixWord, tailWord_7288459, baseEnd_7288459] using wordTrace_append hprefix tailTrace_7288459
  have hstable : (prefixWord ++ tailWord_7288459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288459).length < 2 ^ (prefixWord ++ tailWord_7288459).sum := by decide
  have hdescent : baseEnd_7288459 < baseStart_7288459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288509 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_7288509 : Nat := 118140960795 + 7288509 * 2 ^ 59
def prefixEnd_7288509 : Nat := 4983230072969 + 3 ^ 40 * 7288509 * 2
def baseEnd_7288509 : Nat := 1247502790540243136239421

theorem tailTrace_7288509 : CollatzResearch.WordTrace tailWord_7288509 prefixEnd_7288509 1247502790540243136239421 := by
  unfold tailWord_7288509
  simp only [CollatzResearch.WordTrace]
  refine ⟨265833762351984146080452581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177222508234656097386968387 265833762351984146080452581)
  ·
    refine ⟨49843830440997027390084859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265833762351984146080452581 49843830440997027390084859)
    ·
      refine ⟨74765745661495541085127289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49843830440997027390084859 74765745661495541085127289)
      ·
        refine ⟨56074309246121655813845467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74765745661495541085127289 56074309246121655813845467)
        ·
          refine ⟨84111463869182483720768201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56074309246121655813845467 84111463869182483720768201)
          ·
            refine ⟨63083597901886862790576151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84111463869182483720768201 63083597901886862790576151)
            ·
              refine ⟨94625396852830294185864227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63083597901886862790576151 94625396852830294185864227)
              ·
                refine ⟨141938095279245441278796341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94625396852830294185864227 141938095279245441278796341)
                ·
                  refine ⟨13306696432429260119887157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141938095279245441278796341 13306696432429260119887157)
                  ·
                    refine ⟨1247502790540243136239421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13306696432429260119887157 1247502790540243136239421)
                    ·
                      rfl

theorem cell23_7288509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_7288509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288509 prefixEnd_7288509 := by exact prefixLift 7288509
  have htrace : WordTrace (prefixWord ++ tailWord_7288509) baseStart_7288509 baseEnd_7288509 := by
    simpa [prefixWord, tailWord_7288509, baseEnd_7288509] using wordTrace_append hprefix tailTrace_7288509
  have hstable : (prefixWord ++ tailWord_7288509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288509).length < 2 ^ (prefixWord ++ tailWord_7288509).sum := by decide
  have hdescent : baseEnd_7288509 < baseStart_7288509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288526 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_7288526 : Nat := 118140960795 + 7288526 * 2 ^ 59
def prefixEnd_7288526 : Nat := 4983230072969 + 3 ^ 40 * 7288526 * 2
def baseEnd_7288526 : Nat := 1247505700263951947401895

theorem tailTrace_7288526 : CollatzResearch.WordTrace tailWord_7288526 prefixEnd_7288526 1247505700263951947401895 := by
  unfold tailWord_7288526
  simp only [CollatzResearch.WordTrace]
  refine ⟨33229297799115319747977679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 177222921595281705322547621 33229297799115319747977679)
  ·
    refine ⟨49843946698672979621966519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33229297799115319747977679 49843946698672979621966519)
    ·
      refine ⟨74765920048009469432949779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49843946698672979621966519 74765920048009469432949779)
      ·
        refine ⟨112148880072014204149424669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74765920048009469432949779 112148880072014204149424669)
        ·
          refine ⟨42055830027005326556034251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112148880072014204149424669 42055830027005326556034251)
          ·
            refine ⟨63083745040507989834051377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42055830027005326556034251 63083745040507989834051377)
            ·
              refine ⟨47312808780380992375538533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63083745040507989834051377 47312808780380992375538533)
              ·
                refine ⟨8871151646321436070413475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47312808780380992375538533 8871151646321436070413475)
                ·
                  refine ⟨13306727469482154105620213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8871151646321436070413475 13306727469482154105620213)
                  ·
                    refine ⟨1247505700263951947401895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13306727469482154105620213 1247505700263951947401895)
                    ·
                      rfl

theorem cell23_7288526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_7288526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288526 prefixEnd_7288526 := by exact prefixLift 7288526
  have htrace : WordTrace (prefixWord ++ tailWord_7288526) baseStart_7288526 baseEnd_7288526 := by
    simpa [prefixWord, tailWord_7288526, baseEnd_7288526] using wordTrace_append hprefix tailTrace_7288526
  have hstable : (prefixWord ++ tailWord_7288526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288526).length < 2 ^ (prefixWord ++ tailWord_7288526).sum := by decide
  have hdescent : baseEnd_7288526 < baseStart_7288526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288534 : List Nat := [5, 2, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_7288534 : Nat := 118140960795 + 7288534 * 2 ^ 59
def prefixEnd_7288534 : Nat := 4983230072969 + 3 ^ 40 * 7288534 * 2
def baseEnd_7288534 : Nat := 1247507069545697270301883

theorem tailTrace_7288534 : CollatzResearch.WordTrace tailWord_7288534 prefixEnd_7288534 1247507069545697270301883 := by
  unfold tailWord_7288534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614667136055848459382041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177223116117929050233408437 16614667136055848459382041)
  ·
    refine ⟨12461000352041886344536531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16614667136055848459382041 12461000352041886344536531)
    ·
      refine ⟨18691500528062829516804797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12461000352041886344536531 18691500528062829516804797)
      ·
        refine ⟨7009312698023561068801799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18691500528062829516804797 7009312698023561068801799)
        ·
          refine ⟨10513969047035341603202699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7009312698023561068801799 10513969047035341603202699)
          ·
            refine ⟨15770953570553012404804049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10513969047035341603202699 15770953570553012404804049)
            ·
              refine ⟨11828215177914759303603037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15770953570553012404804049 11828215177914759303603037)
              ·
                refine ⟨4435580691718034738851139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11828215177914759303603037 4435580691718034738851139)
                ·
                  refine ⟨6653371037577052108276709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435580691718034738851139 6653371037577052108276709)
                  ·
                    refine ⟨1247507069545697270301883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6653371037577052108276709 1247507069545697270301883)
                    ·
                      rfl

theorem cell23_7288534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_7288534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288534 prefixEnd_7288534 := by exact prefixLift 7288534
  have htrace : WordTrace (prefixWord ++ tailWord_7288534) baseStart_7288534 baseEnd_7288534 := by
    simpa [prefixWord, tailWord_7288534, baseEnd_7288534] using wordTrace_append hprefix tailTrace_7288534
  have hstable : (prefixWord ++ tailWord_7288534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288534).length < 2 ^ (prefixWord ++ tailWord_7288534).sum := by decide
  have hdescent : baseEnd_7288534 < baseStart_7288534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288559 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_7288559 : Nat := 118140960795 + 7288559 * 2 ^ 59
def prefixEnd_7288559 : Nat := 4983230072969 + 3 ^ 40 * 7288559 * 2
def baseEnd_7288559 : Nat := 3742534045653454213093033

theorem tailTrace_7288559 : CollatzResearch.WordTrace tailWord_7288559 prefixEnd_7288559 3742534045653454213093033 := by
  unfold tailWord_7288559
  simp only [CollatzResearch.WordTrace]
  refine ⟨265835586001803004619772731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177223724001202003079848487 265835586001803004619772731)
  ·
    refine ⟨398753379002704506929659097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265835586001803004619772731 398753379002704506929659097)
    ·
      refine ⟨299065034252028380197244323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398753379002704506929659097 299065034252028380197244323)
      ·
        refine ⟨448597551378042570295866485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299065034252028380197244323 448597551378042570295866485)
        ·
          refine ⟨42056020441691490965237483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 448597551378042570295866485 42056020441691490965237483)
          ·
            refine ⟨63084030662537236447856225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42056020441691490965237483 63084030662537236447856225)
            ·
              refine ⟨47313022996902927335892169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63084030662537236447856225 47313022996902927335892169)
              ·
                refine ⟨35484767247677195501919127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47313022996902927335892169 35484767247677195501919127)
                ·
                  refine ⟨53227150871515793252878691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35484767247677195501919127 53227150871515793252878691)
                  ·
                    refine ⟨79840726307273689879318037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53227150871515793252878691 79840726307273689879318037)
                    ·
                      refine ⟨3742534045653454213093033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79840726307273689879318037 3742534045653454213093033)
                      ·
                        rfl

theorem cell23_7288559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_7288559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288559 prefixEnd_7288559 := by exact prefixLift 7288559
  have htrace : WordTrace (prefixWord ++ tailWord_7288559) baseStart_7288559 baseEnd_7288559 := by
    simpa [prefixWord, tailWord_7288559, baseEnd_7288559] using wordTrace_append hprefix tailTrace_7288559
  have hstable : (prefixWord ++ tailWord_7288559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288559).length < 2 ^ (prefixWord ++ tailWord_7288559).sum := by decide
  have hdescent : baseEnd_7288559 < baseStart_7288559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288563 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 3, 2, 2]
def baseStart_7288563 : Nat := 118140960795 + 7288563 * 2 ^ 59
def prefixEnd_7288563 : Nat := 4983230072969 + 3 ^ 40 * 7288563 * 2
def baseEnd_7288563 : Nat := 3742536099576072197443015

theorem tailTrace_7288563 : CollatzResearch.WordTrace tailWord_7288563 prefixEnd_7288563 3742536099576072197443015 := by
  unfold tailWord_7288563
  simp only [CollatzResearch.WordTrace]
  refine ⟨265835731893788513302918343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177223821262525675535278895 265835731893788513302918343)
  ·
    refine ⟨398753597840682769954377515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265835731893788513302918343 398753597840682769954377515)
    ·
      refine ⟨598130396761024154931566273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398753597840682769954377515 598130396761024154931566273)
      ·
        refine ⟨448597797570768116198674705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598130396761024154931566273 448597797570768116198674705)
        ·
          refine ⟨336448348178076087149006029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448597797570768116198674705 336448348178076087149006029)
          ·
            refine ⟨126168130566778532680877261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336448348178076087149006029 126168130566778532680877261)
            ·
              refine ⟨47313048962541949755328973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126168130566778532680877261 47313048962541949755328973)
              ·
                refine ⟨17742393360953231158248365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47313048962541949755328973 17742393360953231158248365)
                ·
                  refine ⟨6653397510357461684343137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17742393360953231158248365 6653397510357461684343137)
                  ·
                    refine ⟨4990048132768096263257353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653397510357461684343137 4990048132768096263257353)
                    ·
                      refine ⟨3742536099576072197443015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4990048132768096263257353 3742536099576072197443015)
                      ·
                        rfl

theorem cell23_7288563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 2, 2].length) (baseStart_7288563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288563 prefixEnd_7288563 := by exact prefixLift 7288563
  have htrace : WordTrace (prefixWord ++ tailWord_7288563) baseStart_7288563 baseEnd_7288563 := by
    simpa [prefixWord, tailWord_7288563, baseEnd_7288563] using wordTrace_append hprefix tailTrace_7288563
  have hstable : (prefixWord ++ tailWord_7288563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288563).length < 2 ^ (prefixWord ++ tailWord_7288563).sum := by decide
  have hdescent : baseEnd_7288563 < baseStart_7288563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7288566 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7288566 : Nat := 118140960795 + 7288566 * 2 ^ 59
def prefixEnd_7288566 : Nat := 4983230072969 + 3 ^ 40 * 7288566 * 2
def baseEnd_7288566 : Nat := 3742537640018035685705501

theorem tailTrace_7288566 : CollatzResearch.WordTrace tailWord_7288566 prefixEnd_7288566 3742537640018035685705501 := by
  unfold tailWord_7288566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614740082048602800954847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 177223894208518429876851701 16614740082048602800954847)
  ·
    refine ⟨24922110123072904201432271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16614740082048602800954847 24922110123072904201432271)
    ·
      refine ⟨37383165184609356302148407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24922110123072904201432271 37383165184609356302148407)
      ·
        refine ⟨56074747776914034453222611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37383165184609356302148407 56074747776914034453222611)
        ·
          refine ⟨84112121665371051679833917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56074747776914034453222611 84112121665371051679833917)
          ·
            refine ⟨31542045624514144379937719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84112121665371051679833917 31542045624514144379937719)
            ·
              refine ⟨47313068436771216569906579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31542045624514144379937719 47313068436771216569906579)
              ·
                refine ⟨70969602655156824854859869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47313068436771216569906579 70969602655156824854859869)
                ·
                  refine ⟨26613600995683809320572451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70969602655156824854859869 26613600995683809320572451)
                  ·
                    refine ⟨39920401493525713980858677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26613600995683809320572451 39920401493525713980858677)
                    ·
                      refine ⟨3742537640018035685705501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39920401493525713980858677 3742537640018035685705501)
                      ·
                        rfl

theorem cell23_7288566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7288566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7288566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7288566 prefixEnd_7288566 := by exact prefixLift 7288566
  have htrace : WordTrace (prefixWord ++ tailWord_7288566) baseStart_7288566 baseEnd_7288566 := by
    simpa [prefixWord, tailWord_7288566, baseEnd_7288566] using wordTrace_append hprefix tailTrace_7288566
  have hstable : (prefixWord ++ tailWord_7288566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7288566).length < 2 ^ (prefixWord ++ tailWord_7288566).sum := by decide
  have hdescent : baseEnd_7288566 < baseStart_7288566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7288566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
