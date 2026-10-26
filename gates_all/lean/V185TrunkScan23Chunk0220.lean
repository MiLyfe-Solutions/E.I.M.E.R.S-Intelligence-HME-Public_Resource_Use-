import V185TrunkScan23Chunk0219

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1301285 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_1301285 : Nat := 118140960795 + 1301285 * 2 ^ 59
def prefixEnd_1301285 : Nat := 4983230072969 + 3 ^ 40 * 1301285 * 2
def baseEnd_1301285 : Nat := 668184673486046450153005

theorem tailTrace_1301285 : CollatzResearch.WordTrace tailWord_1301285 prefixEnd_1301285 668184673486046450153005 := by
  unfold tailWord_1301285
  simp only [CollatzResearch.WordTrace]
  refine ⟨47461763090674161629537309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31641175393782774419691539 47461763090674161629537309)
  ·
    refine ⟨17798161159002810611076491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47461763090674161629537309 17798161159002810611076491)
    ·
      refine ⟨26697241738504215916614737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17798161159002810611076491 26697241738504215916614737)
      ·
        refine ⟨20022931303878161937461053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26697241738504215916614737 20022931303878161937461053)
        ·
          refine ⟨7508599238954310726547895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20022931303878161937461053 7508599238954310726547895)
          ·
            refine ⟨11262898858431466089821843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7508599238954310726547895 11262898858431466089821843)
            ·
              refine ⟨16894348287647199134732765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262898858431466089821843 16894348287647199134732765)
              ·
                refine ⟨6335380607867699675524787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16894348287647199134732765 6335380607867699675524787)
                ·
                  refine ⟨9503070911801549513287181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6335380607867699675524787 9503070911801549513287181)
                  ·
                    refine ⟨3563651591925581067482693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9503070911801549513287181 3563651591925581067482693)
                    ·
                      refine ⟨668184673486046450153005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3563651591925581067482693 668184673486046450153005)
                      ·
                        rfl

theorem cell23_1301285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_1301285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301285 prefixEnd_1301285 := by exact prefixLift 1301285
  have htrace : WordTrace (prefixWord ++ tailWord_1301285) baseStart_1301285 baseEnd_1301285 := by
    simpa [prefixWord, tailWord_1301285, baseEnd_1301285] using wordTrace_append hprefix tailTrace_1301285
  have hstable : (prefixWord ++ tailWord_1301285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301285).length < 2 ^ (prefixWord ++ tailWord_1301285).sum := by decide
  have hdescent : baseEnd_1301285 < baseStart_1301285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301386 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1301386 : Nat := 118140960795 + 1301386 * 2 ^ 59
def prefixEnd_1301386 : Nat := 4983230072969 + 3 ^ 40 * 1301386 * 2
def baseEnd_1301386 : Nat := 668236535032150554990041

theorem tailTrace_1301386 : CollatzResearch.WordTrace tailWord_1301386 prefixEnd_1301386 668236535032150554990041 := by
  unfold tailWord_1301386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11866361715827063969741003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31643631242205503919309341 11866361715827063969741003)
  ·
    refine ⟨17799542573740595954611505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11866361715827063969741003 17799542573740595954611505)
    ·
      refine ⟨13349656930305446965958629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17799542573740595954611505 13349656930305446965958629)
      ·
        refine ⟨2503060674432271306117243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13349656930305446965958629 2503060674432271306117243)
        ·
          refine ⟨3754591011648406959175865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503060674432271306117243 3754591011648406959175865)
          ·
            refine ⟨2815943258736305219381899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3754591011648406959175865 2815943258736305219381899)
            ·
              refine ⟨4223914888104457829072849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815943258736305219381899 4223914888104457829072849)
              ·
                refine ⟨3167936166078343371804637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4223914888104457829072849 3167936166078343371804637)
                ·
                  refine ⟨1187976062279378764426739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3167936166078343371804637 1187976062279378764426739)
                  ·
                    refine ⟨1781964093419068146640109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1187976062279378764426739 1781964093419068146640109)
                    ·
                      refine ⟨668236535032150554990041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1781964093419068146640109 668236535032150554990041)
                      ·
                        rfl

theorem cell23_1301386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1301386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301386 prefixEnd_1301386 := by exact prefixLift 1301386
  have htrace : WordTrace (prefixWord ++ tailWord_1301386) baseStart_1301386 baseEnd_1301386 := by
    simpa [prefixWord, tailWord_1301386, baseEnd_1301386] using wordTrace_append hprefix tailTrace_1301386
  have hstable : (prefixWord ++ tailWord_1301386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301386).length < 2 ^ (prefixWord ++ tailWord_1301386).sum := by decide
  have hdescent : baseEnd_1301386 < baseStart_1301386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301395 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5]
def baseStart_1301395 : Nat := 118140960795 + 1301395 * 2 ^ 59
def prefixEnd_1301395 : Nat := 4983230072969 + 3 ^ 40 * 1301395 * 2
def baseEnd_1301395 : Nat := 668241156358041019777499

theorem tailTrace_1301395 : CollatzResearch.WordTrace tailWord_1301395 prefixEnd_1301395 668241156358041019777499 := by
  unfold tailWord_1301395
  simp only [CollatzResearch.WordTrace]
  refine ⟨47465775120275650416041639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31643850080183766944027759 47465775120275650416041639)
  ·
    refine ⟨71198662680413475624062459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47465775120275650416041639 71198662680413475624062459)
    ·
      refine ⟨106797994020620213436093689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71198662680413475624062459 106797994020620213436093689)
      ·
        refine ⟨80098495515465160077070267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106797994020620213436093689 80098495515465160077070267)
        ·
          refine ⟨120147743273197740115605401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80098495515465160077070267 120147743273197740115605401)
          ·
            refine ⟨90110807454898305086704051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120147743273197740115605401 90110807454898305086704051)
            ·
              refine ⟨135166211182347457630056077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90110807454898305086704051 135166211182347457630056077)
              ·
                refine ⟨50687329193380296611271029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135166211182347457630056077 50687329193380296611271029)
                ·
                  refine ⟨4751937111879402807306659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50687329193380296611271029 4751937111879402807306659)
                  ·
                    refine ⟨7127905667819104210959989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751937111879402807306659 7127905667819104210959989)
                    ·
                      refine ⟨668241156358041019777499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7127905667819104210959989 668241156358041019777499)
                      ·
                        rfl

theorem cell23_1301395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_1301395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301395 prefixEnd_1301395 := by exact prefixLift 1301395
  have htrace : WordTrace (prefixWord ++ tailWord_1301395) baseStart_1301395 baseEnd_1301395 := by
    simpa [prefixWord, tailWord_1301395, baseEnd_1301395] using wordTrace_append hprefix tailTrace_1301395
  have hstable : (prefixWord ++ tailWord_1301395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301395).length < 2 ^ (prefixWord ++ tailWord_1301395).sum := by decide
  have hdescent : baseEnd_1301395 < baseStart_1301395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301412 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_1301412 : Nat := 118140960795 + 1301412 * 2 ^ 59
def prefixEnd_1301412 : Nat := 4983230072969 + 3 ^ 40 * 1301412 * 2
def baseEnd_1301412 : Nat := 668249885529167453264921

theorem tailTrace_1301412 : CollatzResearch.WordTrace tailWord_1301412 prefixEnd_1301412 668249885529167453264921 := by
  unfold tailWord_1301412
  simp only [CollatzResearch.WordTrace]
  refine ⟨23733197580607031159705245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31644263440809374879606993 23733197580607031159705245)
  ·
    refine ⟨8899949092727636684889467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23733197580607031159705245 8899949092727636684889467)
    ·
      refine ⟨13349923639091455027334201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8899949092727636684889467 13349923639091455027334201)
      ·
        refine ⟨10012442729318591270500651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13349923639091455027334201 10012442729318591270500651)
        ·
          refine ⟨15018664093977886905750977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10012442729318591270500651 15018664093977886905750977)
          ·
            refine ⟨11263998070483415179313233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15018664093977886905750977 11263998070483415179313233)
            ·
              refine ⟨8447998552862561384484925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11263998070483415179313233 8447998552862561384484925)
              ·
                refine ⟨3167999457323460519181847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8447998552862561384484925 3167999457323460519181847)
                ·
                  refine ⟨4751999185985190778772771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167999457323460519181847 4751999185985190778772771)
                  ·
                    refine ⟨7127998778977786168159157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4751999185985190778772771 7127998778977786168159157)
                    ·
                      refine ⟨668249885529167453264921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7127998778977786168159157 668249885529167453264921)
                      ·
                        rfl

theorem cell23_1301412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_1301412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301412 prefixEnd_1301412 := by exact prefixLift 1301412
  have htrace : WordTrace (prefixWord ++ tailWord_1301412) baseStart_1301412 baseEnd_1301412 := by
    simpa [prefixWord, tailWord_1301412, baseEnd_1301412] using wordTrace_append hprefix tailTrace_1301412
  have hstable : (prefixWord ++ tailWord_1301412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301412).length < 2 ^ (prefixWord ++ tailWord_1301412).sum := by decide
  have hdescent : baseEnd_1301412 < baseStart_1301412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301445 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_1301445 : Nat := 118140960795 + 1301445 * 2 ^ 59
def prefixEnd_1301445 : Nat := 4983230072969 + 3 ^ 40 * 1301445 * 2
def baseEnd_1301445 : Nat := 222755610130255274717423

theorem tailTrace_1301445 : CollatzResearch.WordTrace tailWord_1301445 prefixEnd_1301445 222755610130255274717423 := by
  unfold tailWord_1301445
  simp only [CollatzResearch.WordTrace]
  refine ⟨47467598770094508955361789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31645065846729672636907859 47467598770094508955361789)
  ·
    refine ⟨17800349538785440858260671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47467598770094508955361789 17800349538785440858260671)
    ·
      refine ⟨26700524308178161287391007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17800349538785440858260671 26700524308178161287391007)
      ·
        refine ⟨40050786462267241931086511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26700524308178161287391007 40050786462267241931086511)
        ·
          refine ⟨60076179693400862896629767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40050786462267241931086511 60076179693400862896629767)
          ·
            refine ⟨90114269540101294344944651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60076179693400862896629767 90114269540101294344944651)
            ·
              refine ⟨135171404310151941517416977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90114269540101294344944651 135171404310151941517416977)
              ·
                refine ⟨101378553232613956138062733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135171404310151941517416977 101378553232613956138062733)
                ·
                  refine ⟨38016957462230233551773525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101378553232613956138062733 38016957462230233551773525)
                  ·
                    refine ⟨222755610130255274717423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38016957462230233551773525 222755610130255274717423)
                    ·
                      rfl

theorem cell23_1301445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_1301445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301445 prefixEnd_1301445 := by exact prefixLift 1301445
  have htrace : WordTrace (prefixWord ++ tailWord_1301445) baseStart_1301445 baseEnd_1301445 := by
    simpa [prefixWord, tailWord_1301445, baseEnd_1301445] using wordTrace_append hprefix tailTrace_1301445
  have hstable : (prefixWord ++ tailWord_1301445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301445).length < 2 ^ (prefixWord ++ tailWord_1301445).sum := by decide
  have hdescent : baseEnd_1301445 < baseStart_1301445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301460 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1301460 : Nat := 118140960795 + 1301460 * 2 ^ 59
def prefixEnd_1301460 : Nat := 4983230072969 + 3 ^ 40 * 1301460 * 2
def baseEnd_1301460 : Nat := 668274532600583265464701

theorem tailTrace_1301460 : CollatzResearch.WordTrace tailWord_1301460 prefixEnd_1301460 668274532600583265464701 := by
  unfold tailWord_1301460
  simp only [CollatzResearch.WordTrace]
  refine ⟨23734072932520083258578917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31645430576693444344771889 23734072932520083258578917)
  ·
    refine ⟨4450138674847515610983547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23734072932520083258578917 4450138674847515610983547)
    ·
      refine ⟨6675208012271273416475321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4450138674847515610983547 6675208012271273416475321)
      ·
        refine ⟨5006406009203455062356491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6675208012271273416475321 5006406009203455062356491)
        ·
          refine ⟨7509609013805182593534737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5006406009203455062356491 7509609013805182593534737)
          ·
            refine ⟨5632206760353886945151053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7509609013805182593534737 5632206760353886945151053)
            ·
              refine ⟨2112077535132707604431645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5632206760353886945151053 2112077535132707604431645)
              ·
                refine ⟨792029075674765351661867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2112077535132707604431645 792029075674765351661867)
                ·
                  refine ⟨1188043613512148027492801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792029075674765351661867 1188043613512148027492801)
                  ·
                    refine ⟨891032710134111020619601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188043613512148027492801 891032710134111020619601)
                    ·
                      refine ⟨668274532600583265464701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891032710134111020619601 668274532600583265464701)
                      ·
                        rfl

theorem cell23_1301460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1301460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301460 prefixEnd_1301460 := by exact prefixLift 1301460
  have htrace : WordTrace (prefixWord ++ tailWord_1301460) baseStart_1301460 baseEnd_1301460 := by
    simpa [prefixWord, tailWord_1301460, baseEnd_1301460] using wordTrace_append hprefix tailTrace_1301460
  have hstable : (prefixWord ++ tailWord_1301460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301460).length < 2 ^ (prefixWord ++ tailWord_1301460).sum := by decide
  have hdescent : baseEnd_1301460 < baseStart_1301460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301477 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1301477 : Nat := 118140960795 + 1301477 * 2 ^ 59
def prefixEnd_1301477 : Nat := 4983230072969 + 3 ^ 40 * 1301477 * 2
def baseEnd_1301477 : Nat := 668283261771709698952123

theorem tailTrace_1301477 : CollatzResearch.WordTrace tailWord_1301477 prefixEnd_1301477 668283261771709698952123 := by
  unfold tailWord_1301477
  simp only [CollatzResearch.WordTrace]
  refine ⟨47468765905978578420526685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31645843937319052280351123 47468765905978578420526685)
  ·
    refine ⟨17800787214741966907697507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47468765905978578420526685 17800787214741966907697507)
    ·
      refine ⟨26701180822112950361546261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17800787214741966907697507 26701180822112950361546261)
      ·
        refine ⟨1251617851036544548197481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26701180822112950361546261 1251617851036544548197481)
        ·
          refine ⟨938713388277408411148111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251617851036544548197481 938713388277408411148111)
          ·
            refine ⟨1408070082416112616722167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938713388277408411148111 1408070082416112616722167)
            ·
              refine ⟨2112105123624168925083251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408070082416112616722167 2112105123624168925083251)
              ·
                refine ⟨3168157685436253387624877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112105123624168925083251 3168157685436253387624877)
                ·
                  refine ⟨1188059132038595020359329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3168157685436253387624877 1188059132038595020359329)
                  ·
                    refine ⟨891044349028946265269497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188059132038595020359329 891044349028946265269497)
                    ·
                      refine ⟨668283261771709698952123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891044349028946265269497 668283261771709698952123)
                      ·
                        rfl

theorem cell23_1301477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1301477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301477 prefixEnd_1301477 := by exact prefixLift 1301477
  have htrace : WordTrace (prefixWord ++ tailWord_1301477) baseStart_1301477 baseEnd_1301477 := by
    simpa [prefixWord, tailWord_1301477, baseEnd_1301477] using wordTrace_append hprefix tailTrace_1301477
  have hstable : (prefixWord ++ tailWord_1301477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301477).length < 2 ^ (prefixWord ++ tailWord_1301477).sum := by decide
  have hdescent : baseEnd_1301477 < baseStart_1301477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301499 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 1, 4, 2]
def baseStart_1301499 : Nat := 118140960795 + 1301499 * 2 ^ 59
def prefixEnd_1301499 : Nat := 4983230072969 + 3 ^ 40 * 1301499 * 2
def baseEnd_1301499 : Nat := 668294558346108612877021

theorem tailTrace_1301499 : CollatzResearch.WordTrace tailWord_1301499 prefixEnd_1301499 668294558346108612877021 := by
  unfold tailWord_1301499
  simp only [CollatzResearch.WordTrace]
  refine ⟨47469568311898876177827551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31646378874599250785218367 47469568311898876177827551)
  ·
    refine ⟨71204352467848314266741327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47469568311898876177827551 71204352467848314266741327)
    ·
      refine ⟨106806528701772471400111991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71204352467848314266741327 106806528701772471400111991)
      ·
        refine ⟨160209793052658707100167987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106806528701772471400111991 160209793052658707100167987)
        ·
          refine ⟨240314689578988060650251981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160209793052658707100167987 240314689578988060650251981)
          ·
            refine ⟨90118008592120522743844493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240314689578988060650251981 90118008592120522743844493)
            ·
              refine ⟨33794253222045196028941685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90118008592120522743844493 33794253222045196028941685)
              ·
                refine ⟨3168211239566737127713283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33794253222045196028941685 3168211239566737127713283)
                ·
                  refine ⟨4752316859350105691569925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168211239566737127713283 4752316859350105691569925)
                  ·
                    refine ⟨891059411128144817169361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752316859350105691569925 891059411128144817169361)
                    ·
                      refine ⟨668294558346108612877021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891059411128144817169361 668294558346108612877021)
                      ·
                        rfl

theorem cell23_1301499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 4, 2].length) (baseStart_1301499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301499 prefixEnd_1301499 := by exact prefixLift 1301499
  have htrace : WordTrace (prefixWord ++ tailWord_1301499) baseStart_1301499 baseEnd_1301499 := by
    simpa [prefixWord, tailWord_1301499, baseEnd_1301499] using wordTrace_append hprefix tailTrace_1301499
  have hstable : (prefixWord ++ tailWord_1301499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301499).length < 2 ^ (prefixWord ++ tailWord_1301499).sum := by decide
  have hdescent : baseEnd_1301499 < baseStart_1301499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301516 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 1, 4, 2]
def baseStart_1301516 : Nat := 118140960795 + 1301516 * 2 ^ 59
def prefixEnd_1301516 : Nat := 4983230072969 + 3 ^ 40 * 1301516 * 2
def baseEnd_1301516 : Nat := 668303287517235046364443

theorem tailTrace_1301516 : CollatzResearch.WordTrace tailWord_1301516 prefixEnd_1301516 668303287517235046364443 := by
  unfold tailWord_1301516
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735094176418644040598201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31646792235224858720797601 23735094176418644040598201)
  ·
    refine ⟨17801320632313983030448651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23735094176418644040598201 17801320632313983030448651)
    ·
      refine ⟨26701980948470974545672977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17801320632313983030448651 26701980948470974545672977)
      ·
        refine ⟨20026485711353230909254733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26701980948470974545672977 20026485711353230909254733)
        ·
          refine ⟨7509932141757461590970525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20026485711353230909254733 7509932141757461590970525)
          ·
            refine ⟨2816224553159048096613947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7509932141757461590970525 2816224553159048096613947)
            ·
              refine ⟨4224336829738572144920921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816224553159048096613947 4224336829738572144920921)
              ·
                refine ⟨3168252622303929108690691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224336829738572144920921 3168252622303929108690691)
                ·
                  refine ⟨4752378933455893663036037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168252622303929108690691 4752378933455893663036037)
                  ·
                    refine ⟨891071050022980061819257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4752378933455893663036037 891071050022980061819257)
                    ·
                      refine ⟨668303287517235046364443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891071050022980061819257 668303287517235046364443)
                      ·
                        rfl

theorem cell23_1301516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_1301516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301516 prefixEnd_1301516 := by exact prefixLift 1301516
  have htrace : WordTrace (prefixWord ++ tailWord_1301516) baseStart_1301516 baseEnd_1301516 := by
    simpa [prefixWord, tailWord_1301516, baseEnd_1301516] using wordTrace_append hprefix tailTrace_1301516
  have hstable : (prefixWord ++ tailWord_1301516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301516).length < 2 ^ (prefixWord ++ tailWord_1301516).sum := by decide
  have hdescent : baseEnd_1301516 < baseStart_1301516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301546 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1301546 : Nat := 118140960795 + 1301546 * 2 ^ 59
def prefixEnd_1301546 : Nat := 4983230072969 + 3 ^ 40 * 1301546 * 2
def baseEnd_1301546 : Nat := 668318691936869928989305

theorem tailTrace_1301546 : CollatzResearch.WordTrace tailWord_1301546 prefixEnd_1301546 668318691936869928989305 := by
  unfold tailWord_1301546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867820635682150801197123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31647521695152402136525661 11867820635682150801197123)
  ·
    refine ⟨17801730953523226201795685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11867820635682150801197123 17801730953523226201795685)
    ·
      refine ⟨3337824553785604912836691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17801730953523226201795685 3337824553785604912836691)
      ·
        refine ⟨5006736830678407369255037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337824553785604912836691 5006736830678407369255037)
        ·
          refine ⟨1877526311504402763470639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5006736830678407369255037 1877526311504402763470639)
          ·
            refine ⟨2816289467256604145205959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877526311504402763470639 2816289467256604145205959)
            ·
              refine ⟨4224434200884906217808939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816289467256604145205959 4224434200884906217808939)
              ·
                refine ⟨6336651301327359326713409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4224434200884906217808939 6336651301327359326713409)
                ·
                  refine ⟨4752488475995519495035057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6336651301327359326713409 4752488475995519495035057)
                  ·
                    refine ⟨3564366356996639621276293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4752488475995519495035057 3564366356996639621276293)
                    ·
                      refine ⟨668318691936869928989305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3564366356996639621276293 668318691936869928989305)
                      ·
                        rfl

theorem cell23_1301546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1301546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301546 prefixEnd_1301546 := by exact prefixLift 1301546
  have htrace : WordTrace (prefixWord ++ tailWord_1301546) baseStart_1301546 baseEnd_1301546 := by
    simpa [prefixWord, tailWord_1301546, baseEnd_1301546] using wordTrace_append hprefix tailTrace_1301546
  have hstable : (prefixWord ++ tailWord_1301546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301546).length < 2 ^ (prefixWord ++ tailWord_1301546).sum := by decide
  have hdescent : baseEnd_1301546 < baseStart_1301546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301552 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_1301552 : Nat := 118140960795 + 1301552 * 2 ^ 59
def prefixEnd_1301552 : Nat := 4983230072969 + 3 ^ 40 * 1301552 * 2
def baseEnd_1301552 : Nat := 222773924273598968504759

theorem tailTrace_1301552 : CollatzResearch.WordTrace tailWord_1301552 prefixEnd_1301552 222773924273598968504759 := by
  unfold tailWord_1301552
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735750690353433114753455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31647667587137910819671273 23735750690353433114753455)
  ·
    refine ⟨35603626035530149672130183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23735750690353433114753455 35603626035530149672130183)
    ·
      refine ⟨53405439053295224508195275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35603626035530149672130183 53405439053295224508195275)
      ·
        refine ⟨80108158579942836762292913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53405439053295224508195275 80108158579942836762292913)
        ·
          refine ⟨60081118934957127571719685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80108158579942836762292913 60081118934957127571719685)
          ·
            refine ⟨11265209800304461419697441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60081118934957127571719685 11265209800304461419697441)
            ·
              refine ⟨8448907350228346064773081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11265209800304461419697441 8448907350228346064773081)
              ·
                refine ⟨6336680512671259548579811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8448907350228346064773081 6336680512671259548579811)
                ·
                  refine ⟨9505020769006889322869717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6336680512671259548579811 9505020769006889322869717)
                  ·
                    refine ⟨222773924273598968504759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9505020769006889322869717 222773924273598968504759)
                    ·
                      rfl

theorem cell23_1301552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_1301552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301552 prefixEnd_1301552 := by exact prefixLift 1301552
  have htrace : WordTrace (prefixWord ++ tailWord_1301552) baseStart_1301552 baseEnd_1301552 := by
    simpa [prefixWord, tailWord_1301552, baseEnd_1301552] using wordTrace_append hprefix tailTrace_1301552
  have hstable : (prefixWord ++ tailWord_1301552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301552).length < 2 ^ (prefixWord ++ tailWord_1301552).sum := by decide
  have hdescent : baseEnd_1301552 < baseStart_1301552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301556 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1301556 : Nat := 118140960795 + 1301556 * 2 ^ 59
def prefixEnd_1301556 : Nat := 4983230072969 + 3 ^ 40 * 1301556 * 2
def baseEnd_1301556 : Nat := 74258202971490543318251

theorem tailTrace_1301556 : CollatzResearch.WordTrace tailWord_1301556 prefixEnd_1301556 74258202971490543318251 := by
  unfold tailWord_1301556
  simp only [CollatzResearch.WordTrace]
  refine ⟨23735823636346187456326261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31647764848461583275101681 23735823636346187456326261)
  ·
    refine ⟨2225233465907455074030587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23735823636346187456326261 2225233465907455074030587)
    ·
      refine ⟨3337850198861182611045881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225233465907455074030587 3337850198861182611045881)
      ·
        refine ⟨2503387649145886958284411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3337850198861182611045881 2503387649145886958284411)
        ·
          refine ⟨3755081473718830437426617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503387649145886958284411 3755081473718830437426617)
          ·
            refine ⟨2816311105289122828069963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3755081473718830437426617 2816311105289122828069963)
            ·
              refine ⟨4224466657933684242104945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816311105289122828069963 4224466657933684242104945)
              ·
                refine ⟨3168349993450263181578709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4224466657933684242104945 3168349993450263181578709)
                ·
                  refine ⟨74258202971490543318251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3168349993450263181578709 74258202971490543318251)
                  ·
                    rfl

theorem cell23_1301556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1301556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301556 prefixEnd_1301556 := by exact prefixLift 1301556
  have htrace : WordTrace (prefixWord ++ tailWord_1301556) baseStart_1301556 baseEnd_1301556 := by
    simpa [prefixWord, tailWord_1301556, baseEnd_1301556] using wordTrace_append hprefix tailTrace_1301556
  have hstable : (prefixWord ++ tailWord_1301556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301556).length < 2 ^ (prefixWord ++ tailWord_1301556).sum := by decide
  have hdescent : baseEnd_1301556 < baseStart_1301556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301559 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 4, 5, 2]
def baseStart_1301559 : Nat := 118140960795 + 1301559 * 2 ^ 59
def prefixEnd_1301559 : Nat := 4983230072969 + 3 ^ 40 * 1301559 * 2
def baseEnd_1301559 : Nat := 668325367185378378126745

theorem tailTrace_1301559 : CollatzResearch.WordTrace tailWord_1301559 prefixEnd_1301559 668325367185378378126745 := by
  unfold tailWord_1301559
  simp only [CollatzResearch.WordTrace]
  refine ⟨47471756691681506425011731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31647837794454337616674487 47471756691681506425011731)
  ·
    refine ⟨71207635037522259637517597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47471756691681506425011731 71207635037522259637517597)
    ·
      refine ⟨26702863139070847364069099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71207635037522259637517597 26702863139070847364069099)
      ·
        refine ⟨40054294708606271046103649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26702863139070847364069099 40054294708606271046103649)
        ·
          refine ⟨30040721031454703284577737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40054294708606271046103649 30040721031454703284577737)
          ·
            refine ⟨22530540773591027463433303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30040721031454703284577737 22530540773591027463433303)
            ·
              refine ⟨33795811160386541195149955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22530540773591027463433303 33795811160386541195149955)
              ·
                refine ⟨50693716740579811792724933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33795811160386541195149955 50693716740579811792724933)
                ·
                  refine ⟨9505071888858714711135925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50693716740579811792724933 9505071888858714711135925)
                  ·
                    refine ⟨891100489580504504168993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9505071888858714711135925 891100489580504504168993)
                    ·
                      refine ⟨668325367185378378126745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891100489580504504168993 668325367185378378126745)
                      ·
                        rfl

theorem cell23_1301559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_1301559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301559 prefixEnd_1301559 := by exact prefixLift 1301559
  have htrace : WordTrace (prefixWord ++ tailWord_1301559) baseStart_1301559 baseEnd_1301559 := by
    simpa [prefixWord, tailWord_1301559, baseEnd_1301559] using wordTrace_append hprefix tailTrace_1301559
  have hstable : (prefixWord ++ tailWord_1301559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301559).length < 2 ^ (prefixWord ++ tailWord_1301559).sum := by decide
  have hdescent : baseEnd_1301559 < baseStart_1301559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301562 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_1301562 : Nat := 118140960795 + 1301562 * 2 ^ 59
def prefixEnd_1301562 : Nat := 4983230072969 + 3 ^ 40 * 1301562 * 2
def baseEnd_1301562 : Nat := 668326907627341866389231

theorem tailTrace_1301562 : CollatzResearch.WordTrace tailWord_1301562 prefixEnd_1301562 668326907627341866389231 := by
  unfold tailWord_1301562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867966527667659484342735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31647910740447091958247293 11867966527667659484342735)
  ·
    refine ⟨17801949791501489226514103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11867966527667659484342735 17801949791501489226514103)
    ·
      refine ⟨26702924687252233839771155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17801949791501489226514103 26702924687252233839771155)
      ·
        refine ⟨40054387030878350759656733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26702924687252233839771155 40054387030878350759656733)
        ·
          refine ⟨15020395136579381534871275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40054387030878350759656733 15020395136579381534871275)
          ·
            refine ⟨22530592704869072302306913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15020395136579381534871275 22530592704869072302306913)
            ·
              refine ⟨16897944528651804226730185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22530592704869072302306913 16897944528651804226730185)
              ·
                refine ⟨12673458396488853170047639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16897944528651804226730185 12673458396488853170047639)
                ·
                  refine ⟨19010187594733279755071459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12673458396488853170047639 19010187594733279755071459)
                  ·
                    refine ⟨28515281392099919632607189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19010187594733279755071459 28515281392099919632607189)
                    ·
                      refine ⟨668326907627341866389231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28515281392099919632607189 668326907627341866389231)
                      ·
                        rfl

theorem cell23_1301562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_1301562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301562 prefixEnd_1301562 := by exact prefixLift 1301562
  have htrace : WordTrace (prefixWord ++ tailWord_1301562) baseStart_1301562 baseEnd_1301562 := by
    simpa [prefixWord, tailWord_1301562, baseEnd_1301562] using wordTrace_append hprefix tailTrace_1301562
  have hstable : (prefixWord ++ tailWord_1301562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301562).length < 2 ^ (prefixWord ++ tailWord_1301562).sum := by decide
  have hdescent : baseEnd_1301562 < baseStart_1301562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301589 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1301589 : Nat := 118140960795 + 1301589 * 2 ^ 59
def prefixEnd_1301589 : Nat := 4983230072969 + 3 ^ 40 * 1301589 * 2
def baseEnd_1301589 : Nat := 668340771605013260751607

theorem tailTrace_1301589 : CollatzResearch.WordTrace tailWord_1301589 prefixEnd_1301589 668340771605013260751607 := by
  unfold tailWord_1301589
  simp only [CollatzResearch.WordTrace]
  refine ⟨47472850881572821548603821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31648567254381881032402547 47472850881572821548603821)
  ·
    refine ⟨17802319080589808080726433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47472850881572821548603821 17802319080589808080726433)
    ·
      refine ⟨13351739310442356060544825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17802319080589808080726433 13351739310442356060544825)
      ·
        refine ⟨10013804482831767045408619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13351739310442356060544825 10013804482831767045408619)
        ·
          refine ⟨15020706724247650568112929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10013804482831767045408619 15020706724247650568112929)
          ·
            refine ⟨11265530043185737926084697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15020706724247650568112929 11265530043185737926084697)
            ·
              refine ⟨8449147532389303444563523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11265530043185737926084697 8449147532389303444563523)
              ·
                refine ⟨12673721298583955166845285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449147532389303444563523 12673721298583955166845285)
                ·
                  refine ⟨2376322743484491593783491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12673721298583955166845285 2376322743484491593783491)
                  ·
                    refine ⟨3564484115226737390675237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2376322743484491593783491 3564484115226737390675237)
                    ·
                      refine ⟨668340771605013260751607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3564484115226737390675237 668340771605013260751607)
                      ·
                        rfl

theorem cell23_1301589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1301589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301589 prefixEnd_1301589 := by exact prefixLift 1301589
  have htrace : WordTrace (prefixWord ++ tailWord_1301589) baseStart_1301589 baseEnd_1301589 := by
    simpa [prefixWord, tailWord_1301589, baseEnd_1301589] using wordTrace_append hprefix tailTrace_1301589
  have hstable : (prefixWord ++ tailWord_1301589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301589).length < 2 ^ (prefixWord ++ tailWord_1301589).sum := by decide
  have hdescent : baseEnd_1301589 < baseStart_1301589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301609 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_1301609 : Nat := 118140960795 + 1301609 * 2 ^ 59
def prefixEnd_1301609 : Nat := 4983230072969 + 3 ^ 40 * 1301609 * 2
def baseEnd_1301609 : Nat := 668351041218103182501515

theorem tailTrace_1301609 : CollatzResearch.WordTrace tailWord_1301609 prefixEnd_1301609 668351041218103182501515 := by
  unfold tailWord_1301609
  simp only [CollatzResearch.WordTrace]
  refine ⟨47473580341500364964331881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31649053561000243309554587 47473580341500364964331881)
  ·
    refine ⟨35605185256125273723248911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47473580341500364964331881 35605185256125273723248911)
    ·
      refine ⟨53407777884187910584873367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35605185256125273723248911 53407777884187910584873367)
      ·
        refine ⟨80111666826281865877310051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53407777884187910584873367 80111666826281865877310051)
        ·
          refine ⟨120167500239422798815965077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80111666826281865877310051 120167500239422798815965077)
          ·
            refine ⟨5632851573722943694498363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120167500239422798815965077 5632851573722943694498363)
            ·
              refine ⟨8449277360584415541747545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632851573722943694498363 8449277360584415541747545)
              ·
                refine ⟨6336958020438311656310659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8449277360584415541747545 6336958020438311656310659)
                ·
                  refine ⟨9505437030657467484465989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6336958020438311656310659 9505437030657467484465989)
                  ·
                    refine ⟨1782269443248275153337373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9505437030657467484465989 1782269443248275153337373)
                    ·
                      refine ⟨668351041218103182501515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1782269443248275153337373 668351041218103182501515)
                      ·
                        rfl

theorem cell23_1301609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_1301609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301609 prefixEnd_1301609 := by exact prefixLift 1301609
  have htrace : WordTrace (prefixWord ++ tailWord_1301609) baseStart_1301609 baseEnd_1301609 := by
    simpa [prefixWord, tailWord_1301609, baseEnd_1301609] using wordTrace_append hprefix tailTrace_1301609
  have hstable : (prefixWord ++ tailWord_1301609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301609).length < 2 ^ (prefixWord ++ tailWord_1301609).sum := by decide
  have hdescent : baseEnd_1301609 < baseStart_1301609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301689 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_1301689 : Nat := 118140960795 + 1301689 * 2 ^ 59
def prefixEnd_1301689 : Nat := 4983230072969 + 3 ^ 40 * 1301689 * 2
def baseEnd_1301689 : Nat := 222797373223487623167049

theorem tailTrace_1301689 : CollatzResearch.WordTrace tailWord_1301689 prefixEnd_1301689 222797373223487623167049 := by
  unfold tailWord_1301689
  simp only [CollatzResearch.WordTrace]
  refine ⟨47476498181210538627244121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31650998787473692418162747 47476498181210538627244121)
  ·
    refine ⟨35607373635907903970433091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47476498181210538627244121 35607373635907903970433091)
    ·
      refine ⟨53411060453861855955649637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35607373635907903970433091 53411060453861855955649637)
      ·
        refine ⟨10014573835099097991684307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53411060453861855955649637 10014573835099097991684307)
        ·
          refine ⟨15021860752648646987526461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10014573835099097991684307 15021860752648646987526461)
          ·
            refine ⟨5633197782243242620322423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15021860752648646987526461 5633197782243242620322423)
            ·
              refine ⟨8449796673364863930483635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5633197782243242620322423 8449796673364863930483635)
              ·
                refine ⟨12674695010047295895725453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8449796673364863930483635 12674695010047295895725453)
                ·
                  refine ⟨4753010628767735960897045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12674695010047295895725453 4753010628767735960897045)
                  ·
                    refine ⟨222797373223487623167049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4753010628767735960897045 222797373223487623167049)
                    ·
                      rfl

theorem cell23_1301689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_1301689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301689 prefixEnd_1301689 := by exact prefixLift 1301689
  have htrace : WordTrace (prefixWord ++ tailWord_1301689) baseStart_1301689 baseEnd_1301689 := by
    simpa [prefixWord, tailWord_1301689, baseEnd_1301689] using wordTrace_append hprefix tailTrace_1301689
  have hstable : (prefixWord ++ tailWord_1301689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301689).length < 2 ^ (prefixWord ++ tailWord_1301689).sum := by decide
  have hdescent : baseEnd_1301689 < baseStart_1301689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301699 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5]
def baseStart_1301699 : Nat := 118140960795 + 1301699 * 2 ^ 59
def prefixEnd_1301699 : Nat := 4983230072969 + 3 ^ 40 * 1301699 * 2
def baseEnd_1301699 : Nat := 668397254477007830376101

theorem tailTrace_1301699 : CollatzResearch.WordTrace tailWord_1301699 prefixEnd_1301699 668397254477007830376101 := by
  unfold tailWord_1301699
  simp only [CollatzResearch.WordTrace]
  refine ⟨47476862911174310335108151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31651241940782873556738767 47476862911174310335108151)
  ·
    refine ⟨71215294366761465502662227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47476862911174310335108151 71215294366761465502662227)
    ·
      refine ⟨106822941550142198253993341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71215294366761465502662227 106822941550142198253993341)
      ·
        refine ⟨40058603081303324345247503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106822941550142198253993341 40058603081303324345247503)
        ·
          refine ⟨60087904621954986517871255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40058603081303324345247503 60087904621954986517871255)
          ·
            refine ⟨90131856932932479776806883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60087904621954986517871255 90131856932932479776806883)
            ·
              refine ⟨135197785399398719665210325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90131856932932479776806883 135197785399398719665210325)
              ·
                refine ⟨3168698095298407492153367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135197785399398719665210325 3168698095298407492153367)
                ·
                  refine ⟨4753047142947611238230051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3168698095298407492153367 4753047142947611238230051)
                  ·
                    refine ⟨7129570714421416857345077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4753047142947611238230051 7129570714421416857345077)
                    ·
                      refine ⟨668397254477007830376101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7129570714421416857345077 668397254477007830376101)
                      ·
                        rfl

theorem cell23_1301699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_1301699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301699 prefixEnd_1301699 := by exact prefixLift 1301699
  have htrace : WordTrace (prefixWord ++ tailWord_1301699) baseStart_1301699 baseEnd_1301699 := by
    simpa [prefixWord, tailWord_1301699, baseEnd_1301699] using wordTrace_append hprefix tailTrace_1301699
  have hstable : (prefixWord ++ tailWord_1301699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301699).length < 2 ^ (prefixWord ++ tailWord_1301699).sum := by decide
  have hdescent : baseEnd_1301699 < baseStart_1301699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301713 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 3, 2, 2]
def baseStart_1301713 : Nat := 118140960795 + 1301713 * 2 ^ 59
def prefixEnd_1301713 : Nat := 4983230072969 + 3 ^ 40 * 1301713 * 2
def baseEnd_1301713 : Nat := 668404443206170775601037

theorem tailTrace_1301713 : CollatzResearch.WordTrace tailWord_1301713 prefixEnd_1301713 668404443206170775601037 := by
  unfold tailWord_1301713
  simp only [CollatzResearch.WordTrace]
  refine ⟨47477373533123590726117793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31651582355415727150745195 47477373533123590726117793)
  ·
    refine ⟨35608030149842693044588345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47477373533123590726117793 35608030149842693044588345)
    ·
      refine ⟨26706022612382019783441259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35608030149842693044588345 26706022612382019783441259)
      ·
        refine ⟨40059033918573029675161889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26706022612382019783441259 40059033918573029675161889)
        ·
          refine ⟨30044275438929772256371417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40059033918573029675161889 30044275438929772256371417)
          ·
            refine ⟨22533206579197329192278563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30044275438929772256371417 22533206579197329192278563)
            ·
              refine ⟨33799809868795993788417845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22533206579197329192278563 33799809868795993788417845)
              ·
                refine ⟨3168732175199624417664173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33799809868795993788417845 3168732175199624417664173)
                ·
                  refine ⟨1188274565699859156624065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3168732175199624417664173 1188274565699859156624065)
                  ·
                    refine ⟨891205924274894367468049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188274565699859156624065 891205924274894367468049)
                    ·
                      refine ⟨668404443206170775601037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891205924274894367468049 668404443206170775601037)
                      ·
                        rfl

theorem cell23_1301713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_1301713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301713 prefixEnd_1301713 := by exact prefixLift 1301713
  have htrace : WordTrace (prefixWord ++ tailWord_1301713) baseStart_1301713 baseEnd_1301713 := by
    simpa [prefixWord, tailWord_1301713, baseEnd_1301713] using wordTrace_append hprefix tailTrace_1301713
  have hstable : (prefixWord ++ tailWord_1301713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301713).length < 2 ^ (prefixWord ++ tailWord_1301713).sum := by decide
  have hdescent : baseEnd_1301713 < baseStart_1301713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301719 : List Nat := [1, 1, 3, 2, 1, 2, 5, 8]
def baseStart_1301719 : Nat := 118140960795 + 1301719 * 2 ^ 59
def prefixEnd_1301719 : Nat := 4983230072969 + 3 ^ 40 * 1301719 * 2
def baseEnd_1301719 : Nat := 24755834225559176004667

theorem tailTrace_1301719 : CollatzResearch.WordTrace tailWord_1301719 prefixEnd_1301719 24755834225559176004667 := by
  unfold tailWord_1301719
  simp only [CollatzResearch.WordTrace]
  refine ⟨47477592371101853750836211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31651728247401235833890807 47477592371101853750836211)
  ·
    refine ⟨71216388556652780626254317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47477592371101853750836211 71216388556652780626254317)
    ·
      refine ⟨26706145708744792734845369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71216388556652780626254317 26706145708744792734845369)
      ·
        refine ⟨20029609281558594551134027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26706145708744792734845369 20029609281558594551134027)
        ·
          refine ⟨30044413922337891826701041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20029609281558594551134027 30044413922337891826701041)
          ·
            refine ⟨22533310441753418870025781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30044413922337891826701041 22533310441753418870025781)
            ·
              refine ⟨2112497853914383019064917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22533310441753418870025781 2112497853914383019064917)
              ·
                refine ⟨24755834225559176004667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2112497853914383019064917 24755834225559176004667)
                ·
                  rfl

theorem cell23_1301719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 8].length) (baseStart_1301719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301719 prefixEnd_1301719 := by exact prefixLift 1301719
  have htrace : WordTrace (prefixWord ++ tailWord_1301719) baseStart_1301719 baseEnd_1301719 := by
    simpa [prefixWord, tailWord_1301719, baseEnd_1301719] using wordTrace_append hprefix tailTrace_1301719
  have hstable : (prefixWord ++ tailWord_1301719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301719).length < 2 ^ (prefixWord ++ tailWord_1301719).sum := by decide
  have hdescent : baseEnd_1301719 < baseStart_1301719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301736 : List Nat := [2, 1, 4, 1, 2, 1, 5, 7]
def baseStart_1301736 : Nat := 118140960795 + 1301736 * 2 ^ 59
def prefixEnd_1301736 : Nat := 4983230072969 + 3 ^ 40 * 1301736 * 2
def baseEnd_1301736 : Nat := 24756157528193488356053

theorem tailTrace_1301736 : CollatzResearch.WordTrace tailWord_1301736 prefixEnd_1301736 24756157528193488356053 := by
  unfold tailWord_1301736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23739106206020132827102531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31652141608026843769470041 23739106206020132827102531)
  ·
    refine ⟨35608659309030199240653797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23739106206020132827102531 35608659309030199240653797)
    ·
      refine ⟨6676623620443162357622587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35608659309030199240653797 6676623620443162357622587)
      ·
        refine ⟨10014935430664743536433881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676623620443162357622587 10014935430664743536433881)
        ·
          refine ⟨7511201572998557652325411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10014935430664743536433881 7511201572998557652325411)
          ·
            refine ⟨11266802359497836478488117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511201572998557652325411 11266802359497836478488117)
            ·
              refine ⟨1056262721202922169858261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11266802359497836478488117 1056262721202922169858261)
              ·
                refine ⟨24756157528193488356053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1056262721202922169858261 24756157528193488356053)
                ·
                  rfl

theorem cell23_1301736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 7].length) (baseStart_1301736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301736 prefixEnd_1301736 := by exact prefixLift 1301736
  have htrace : WordTrace (prefixWord ++ tailWord_1301736) baseStart_1301736 baseEnd_1301736 := by
    simpa [prefixWord, tailWord_1301736, baseEnd_1301736] using wordTrace_append hprefix tailTrace_1301736
  have hstable : (prefixWord ++ tailWord_1301736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301736).length < 2 ^ (prefixWord ++ tailWord_1301736).sum := by decide
  have hdescent : baseEnd_1301736 < baseStart_1301736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301747 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 1, 2, 2]
def baseStart_1301747 : Nat := 118140960795 + 1301747 * 2 ^ 59
def prefixEnd_1301747 : Nat := 4983230072969 + 3 ^ 40 * 1301747 * 2
def baseEnd_1301747 : Nat := 668421901548423642575881

theorem tailTrace_1301747 : CollatzResearch.WordTrace tailWord_1301747 prefixEnd_1301747 668421901548423642575881 := by
  unfold tailWord_1301747
  simp only [CollatzResearch.WordTrace]
  refine ⟨47478613615000414532855495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31652409076666943021903663 47478613615000414532855495)
  ·
    refine ⟨71217920422500621799283243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47478613615000414532855495 71217920422500621799283243)
    ·
      refine ⟨106826880633750932698924865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71217920422500621799283243 106826880633750932698924865)
      ·
        refine ⟨80120160475313199524193649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106826880633750932698924865 80120160475313199524193649)
        ·
          refine ⟨60090120356484899643145237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80120160475313199524193649 60090120356484899643145237)
          ·
            refine ⟨2816724391710229670772433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60090120356484899643145237 2816724391710229670772433)
            ·
              refine ⟨2112543293782672253079325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2816724391710229670772433 2112543293782672253079325)
              ·
                refine ⟨792203735168502094904747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2112543293782672253079325 792203735168502094904747)
                ·
                  refine ⟨1188305602752753142357121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792203735168502094904747 1188305602752753142357121)
                  ·
                    refine ⟨891229202064564856767841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188305602752753142357121 891229202064564856767841)
                    ·
                      refine ⟨668421901548423642575881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891229202064564856767841 668421901548423642575881)
                      ·
                        rfl

theorem cell23_1301747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 2, 2].length) (baseStart_1301747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301747 prefixEnd_1301747 := by exact prefixLift 1301747
  have htrace : WordTrace (prefixWord ++ tailWord_1301747) baseStart_1301747 baseEnd_1301747 := by
    simpa [prefixWord, tailWord_1301747, baseEnd_1301747] using wordTrace_append hprefix tailTrace_1301747
  have hstable : (prefixWord ++ tailWord_1301747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301747).length < 2 ^ (prefixWord ++ tailWord_1301747).sum := by decide
  have hdescent : baseEnd_1301747 < baseStart_1301747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301763 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 3]
def baseStart_1301763 : Nat := 118140960795 + 1301763 * 2 ^ 59
def prefixEnd_1301763 : Nat := 4983230072969 + 3 ^ 40 * 1301763 * 2
def baseEnd_1301763 : Nat := 668430117238895579975807

theorem tailTrace_1301763 : CollatzResearch.WordTrace tailWord_1301763 prefixEnd_1301763 668430117238895579975807 := by
  unfold tailWord_1301763
  simp only [CollatzResearch.WordTrace]
  refine ⟨47479197182942449265437943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31652798121961632843625295 47479197182942449265437943)
  ·
    refine ⟨71218795774413673898156915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47479197182942449265437943 71218795774413673898156915)
    ·
      refine ⟨106828193661620510847235373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71218795774413673898156915 106828193661620510847235373)
      ·
        refine ⟨40060572623107691567713265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106828193661620510847235373 40060572623107691567713265)
        ·
          refine ⟨30045429467330768675784949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40060572623107691567713265 30045429467330768675784949)
          ·
            refine ⟨2816759012562259563354839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30045429467330768675784949 2816759012562259563354839)
            ·
              refine ⟨4225138518843389345032259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816759012562259563354839 4225138518843389345032259)
              ·
                refine ⟨6337707778265084017548389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225138518843389345032259 6337707778265084017548389)
                ·
                  refine ⟨1188320208424703253290323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6337707778265084017548389 1188320208424703253290323)
                  ·
                    refine ⟨1782480312637054879935485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1188320208424703253290323 1782480312637054879935485)
                    ·
                      refine ⟨668430117238895579975807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1782480312637054879935485 668430117238895579975807)
                      ·
                        rfl

theorem cell23_1301763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_1301763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301763 prefixEnd_1301763 := by exact prefixLift 1301763
  have htrace : WordTrace (prefixWord ++ tailWord_1301763) baseStart_1301763 baseEnd_1301763 := by
    simpa [prefixWord, tailWord_1301763, baseEnd_1301763] using wordTrace_append hprefix tailTrace_1301763
  have hstable : (prefixWord ++ tailWord_1301763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301763).length < 2 ^ (prefixWord ++ tailWord_1301763).sum := by decide
  have hdescent : baseEnd_1301763 < baseStart_1301763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301820 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_1301820 : Nat := 118140960795 + 1301820 * 2 ^ 59
def prefixEnd_1301820 : Nat := 4983230072969 + 3 ^ 40 * 1301820 * 2
def baseEnd_1301820 : Nat := 668459385636201856963045

theorem tailTrace_1301820 : CollatzResearch.WordTrace tailWord_1301820 prefixEnd_1301820 668459385636201856963045 := by
  unfold tailWord_1301820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23740638071867974000131457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31654184095823965333508609 23740638071867974000131457)
  ·
    refine ⟨17805478553900980500098593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23740638071867974000131457 17805478553900980500098593)
    ·
      refine ⟨13354108915425735375073945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17805478553900980500098593 13354108915425735375073945)
      ·
        refine ⟨10015581686569301531305459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13354108915425735375073945 10015581686569301531305459)
        ·
          refine ⟨15023372529853952296958189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10015581686569301531305459 15023372529853952296958189)
          ·
            refine ⟨5633764698695232111359321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15023372529853952296958189 5633764698695232111359321)
            ·
              refine ⟨4225323524021424083519491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5633764698695232111359321 4225323524021424083519491)
              ·
                refine ⟨6337985286032136125279237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225323524021424083519491 6337985286032136125279237)
                ·
                  refine ⟨1188372241131025523489857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6337985286032136125279237 1188372241131025523489857)
                  ·
                    refine ⟨891279180848269142617393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188372241131025523489857 891279180848269142617393)
                    ·
                      refine ⟨668459385636201856963045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891279180848269142617393 668459385636201856963045)
                      ·
                        rfl

theorem cell23_1301820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_1301820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301820 prefixEnd_1301820 := by exact prefixLift 1301820
  have htrace : WordTrace (prefixWord ++ tailWord_1301820) baseStart_1301820 baseEnd_1301820 := by
    simpa [prefixWord, tailWord_1301820, baseEnd_1301820] using wordTrace_append hprefix tailTrace_1301820
  have hstable : (prefixWord ++ tailWord_1301820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301820).length < 2 ^ (prefixWord ++ tailWord_1301820).sum := by decide
  have hdescent : baseEnd_1301820 < baseStart_1301820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301893 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 6, 2]
def baseStart_1301893 : Nat := 118140960795 + 1301893 * 2 ^ 59
def prefixEnd_1301893 : Nat := 4983230072969 + 3 ^ 40 * 1301893 * 2
def baseEnd_1301893 : Nat := 668496869723980071350209

theorem tailTrace_1301893 : CollatzResearch.WordTrace tailWord_1301893 prefixEnd_1301893 668496869723980071350209 := by
  unfold tailWord_1301893
  simp only [CollatzResearch.WordTrace]
  refine ⟨47483938672471481467670333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31655959114980987645113555 47483938672471481467670333)
  ·
    refine ⟨17806477002176805550376375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47483938672471481467670333 17806477002176805550376375)
    ·
      refine ⟨26709715503265208325564563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17806477002176805550376375 26709715503265208325564563)
      ·
        refine ⟨40064573254897812488346845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26709715503265208325564563 40064573254897812488346845)
        ·
          refine ⟨15024214970586679683130067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40064573254897812488346845 15024214970586679683130067)
          ·
            refine ⟨22536322455880019524695101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15024214970586679683130067 22536322455880019524695101)
            ·
              refine ⟨8451120920955007321760663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22536322455880019524695101 8451120920955007321760663)
              ·
                refine ⟨12676681381432510982640995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8451120920955007321760663 12676681381432510982640995)
                ·
                  refine ⟨19015022072148766473961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12676681381432510982640995 19015022072148766473961493)
                  ·
                    refine ⟨891329159631973428466945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19015022072148766473961493 891329159631973428466945)
                    ·
                      refine ⟨668496869723980071350209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891329159631973428466945 668496869723980071350209)
                      ·
                        rfl

theorem cell23_1301893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_1301893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301893 prefixEnd_1301893 := by exact prefixLift 1301893
  have htrace : WordTrace (prefixWord ++ tailWord_1301893) baseStart_1301893 baseEnd_1301893 := by
    simpa [prefixWord, tailWord_1301893, baseEnd_1301893] using wordTrace_append hprefix tailTrace_1301893
  have hstable : (prefixWord ++ tailWord_1301893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301893).length < 2 ^ (prefixWord ++ tailWord_1301893).sum := by decide
  have hdescent : baseEnd_1301893 < baseStart_1301893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301913 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_1301913 : Nat := 118140960795 + 1301913 * 2 ^ 59
def prefixEnd_1301913 : Nat := 4983230072969 + 3 ^ 40 * 1301913 * 2
def baseEnd_1301913 : Nat := 668507139337069993100117

theorem tailTrace_1301913 : CollatzResearch.WordTrace tailWord_1301913 prefixEnd_1301913 668507139337069993100117 := by
  unfold tailWord_1301913
  simp only [CollatzResearch.WordTrace]
  refine ⟨47484668132399024883398393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31656445421599349922265595 47484668132399024883398393)
  ·
    refine ⟨35613501099299268662548795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47484668132399024883398393 35613501099299268662548795)
    ·
      refine ⟨53420251648948902993823193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35613501099299268662548795 53420251648948902993823193)
      ·
        refine ⟨40065188736711677245367395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53420251648948902993823193 40065188736711677245367395)
        ·
          refine ⟨60097783105067515868051093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40065188736711677245367395 60097783105067515868051093)
          ·
            refine ⟨2817083583050039806314895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60097783105067515868051093 2817083583050039806314895)
            ·
              refine ⟨4225625374575059709472343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817083583050039806314895 4225625374575059709472343)
              ·
                refine ⟨6338438061862589564208515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225625374575059709472343 6338438061862589564208515)
                ·
                  refine ⟨9507657092793884346312773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338438061862589564208515 9507657092793884346312773)
                  ·
                    refine ⟨1782685704898853314933645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9507657092793884346312773 1782685704898853314933645)
                    ·
                      refine ⟨668507139337069993100117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1782685704898853314933645 668507139337069993100117)
                      ·
                        rfl

theorem cell23_1301913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_1301913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301913 prefixEnd_1301913 := by exact prefixLift 1301913
  have htrace : WordTrace (prefixWord ++ tailWord_1301913) baseStart_1301913 baseEnd_1301913 := by
    simpa [prefixWord, tailWord_1301913, baseEnd_1301913] using wordTrace_append hprefix tailTrace_1301913
  have hstable : (prefixWord ++ tailWord_1301913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301913).length < 2 ^ (prefixWord ++ tailWord_1301913).sum := by decide
  have hdescent : baseEnd_1301913 < baseStart_1301913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301960 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_1301960 : Nat := 118140960795 + 1301960 * 2 ^ 59
def prefixEnd_1301960 : Nat := 4983230072969 + 3 ^ 40 * 1301960 * 2
def baseEnd_1301960 : Nat := 668531272927831309212401

theorem tailTrace_1301960 : CollatzResearch.WordTrace tailWord_1301960 prefixEnd_1301960 668531272927831309212401 := by
  unfold tailWord_1301960
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743191181614375955179667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31657588242152501273572889 23743191181614375955179667)
  ·
    refine ⟨35614786772421563932769501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743191181614375955179667 35614786772421563932769501)
    ·
      refine ⟨13355545039658086474788563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35614786772421563932769501 13355545039658086474788563)
      ·
        refine ⟨20033317559487129712182845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355545039658086474788563 20033317559487129712182845)
        ·
          refine ⟨7512494084807673642068567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20033317559487129712182845 7512494084807673642068567)
          ·
            refine ⟨11268741127211510463102851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7512494084807673642068567 11268741127211510463102851)
            ·
              refine ⟨16903111690817265694654277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11268741127211510463102851 16903111690817265694654277)
              ·
                refine ⟨3169333442028237317747677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16903111690817265694654277 3169333442028237317747677)
                ·
                  refine ⟨1188500040760588994155379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3169333442028237317747677 1188500040760588994155379)
                  ·
                    refine ⟨1782750061140883491233069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1188500040760588994155379 1782750061140883491233069)
                    ·
                      refine ⟨668531272927831309212401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1782750061140883491233069 668531272927831309212401)
                      ·
                        rfl

theorem cell23_1301960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_1301960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301960 prefixEnd_1301960 := by exact prefixLift 1301960
  have htrace : WordTrace (prefixWord ++ tailWord_1301960) baseStart_1301960 baseEnd_1301960 := by
    simpa [prefixWord, tailWord_1301960, baseEnd_1301960] using wordTrace_append hprefix tailTrace_1301960
  have hstable : (prefixWord ++ tailWord_1301960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301960).length < 2 ^ (prefixWord ++ tailWord_1301960).sum := by decide
  have hdescent : baseEnd_1301960 < baseStart_1301960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301963 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 1, 5]
def baseStart_1301963 : Nat := 118140960795 + 1301963 * 2 ^ 59
def prefixEnd_1301963 : Nat := 4983230072969 + 3 ^ 40 * 1301963 * 2
def baseEnd_1301963 : Nat := 222844271123264932491629

theorem tailTrace_1301963 : CollatzResearch.WordTrace tailWord_1301963 prefixEnd_1301963 222844271123264932491629 := by
  unfold tailWord_1301963
  simp only [CollatzResearch.WordTrace]
  refine ⟨47486491782217883422718543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31657661188145255615145695 47486491782217883422718543)
  ·
    refine ⟨71229737673326825134077815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47486491782217883422718543 71229737673326825134077815)
    ·
      refine ⟨106844606509990237701116723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71229737673326825134077815 106844606509990237701116723)
      ·
        refine ⟨160266909764985356551675085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106844606509990237701116723 160266909764985356551675085)
        ·
          refine ⟨60100091161869508706878157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160266909764985356551675085 60100091161869508706878157)
          ·
            refine ⟨22537534185701065765079309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60100091161869508706878157 22537534185701065765079309)
            ·
              refine ⟨8451575319637899661904741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22537534185701065765079309 8451575319637899661904741)
              ·
                refine ⟨1584670372432106186607139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8451575319637899661904741 1584670372432106186607139)
                ·
                  refine ⟨2377005558648159279910709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584670372432106186607139 2377005558648159279910709)
                  ·
                    refine ⟨222844271123264932491629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2377005558648159279910709 222844271123264932491629)
                    ·
                      rfl

theorem cell23_1301963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 5].length) (baseStart_1301963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301963 prefixEnd_1301963 := by exact prefixLift 1301963
  have htrace : WordTrace (prefixWord ++ tailWord_1301963) baseStart_1301963 baseEnd_1301963 := by
    simpa [prefixWord, tailWord_1301963, baseEnd_1301963] using wordTrace_append hprefix tailTrace_1301963
  have hstable : (prefixWord ++ tailWord_1301963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301963).length < 2 ^ (prefixWord ++ tailWord_1301963).sum := by decide
  have hdescent : baseEnd_1301963 < baseStart_1301963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301987 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 2, 3, 2]
def baseStart_1301987 : Nat := 118140960795 + 1301987 * 2 ^ 59
def prefixEnd_1301987 : Nat := 4983230072969 + 3 ^ 40 * 1301987 * 2
def baseEnd_1301987 : Nat := 668545136905502703574777

theorem tailTrace_1301987 : CollatzResearch.WordTrace tailWord_1301987 prefixEnd_1301987 668545136905502703574777 := by
  unfold tailWord_1301987
  simp only [CollatzResearch.WordTrace]
  refine ⟨47487367134130935521592215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31658244756087290347728143 47487367134130935521592215)
  ·
    refine ⟨71231050701196403282388323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47487367134130935521592215 71231050701196403282388323)
    ·
      refine ⟨106846576051794604923582485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71231050701196403282388323 106846576051794604923582485)
      ·
        refine ⟨5008433252427872105792929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106846576051794604923582485 5008433252427872105792929)
        ·
          refine ⟨3756324939320904079344697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5008433252427872105792929 3756324939320904079344697)
          ·
            refine ⟨2817243704490678059508523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3756324939320904079344697 2817243704490678059508523)
            ·
              refine ⟨4225865556736017089262785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817243704490678059508523 4225865556736017089262785)
              ·
                refine ⟨3169399167552012816947089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4225865556736017089262785 3169399167552012816947089)
                ·
                  refine ⟨2377049375664009612710317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169399167552012816947089 2377049375664009612710317)
                  ·
                    refine ⟨891393515874003604766369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377049375664009612710317 891393515874003604766369)
                    ·
                      refine ⟨668545136905502703574777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891393515874003604766369 668545136905502703574777)
                      ·
                        rfl

theorem cell23_1301987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_1301987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301987 prefixEnd_1301987 := by exact prefixLift 1301987
  have htrace : WordTrace (prefixWord ++ tailWord_1301987) baseStart_1301987 baseEnd_1301987 := by
    simpa [prefixWord, tailWord_1301987, baseEnd_1301987] using wordTrace_append hprefix tailTrace_1301987
  have hstable : (prefixWord ++ tailWord_1301987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301987).length < 2 ^ (prefixWord ++ tailWord_1301987).sum := by decide
  have hdescent : baseEnd_1301987 < baseStart_1301987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301994 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_1301994 : Nat := 118140960795 + 1301994 * 2 ^ 59
def prefixEnd_1301994 : Nat := 4983230072969 + 3 ^ 40 * 1301994 * 2
def baseEnd_1301994 : Nat := 668548731270084176187245

theorem tailTrace_1301994 : CollatzResearch.WordTrace tailWord_1301994 prefixEnd_1301994 668548731270084176187245 := by
  unfold tailWord_1301994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871905611276393929274259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31658414963403717144731357 11871905611276393929274259)
  ·
    refine ⟨17807858416914590893911389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11871905611276393929274259 17807858416914590893911389)
    ·
      refine ⟨6677946906342971585216771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17807858416914590893911389 6677946906342971585216771)
      ·
        refine ⟨10016920359514457377825157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677946906342971585216771 10016920359514457377825157)
        ·
          refine ⟨1878172567408960758342217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10016920359514457377825157 1878172567408960758342217)
          ·
            refine ⟨1408629425556720568756663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878172567408960758342217 1408629425556720568756663)
            ·
              refine ⟨2112944138335080853134995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408629425556720568756663 2112944138335080853134995)
              ·
                refine ⟨3169416207502621279702493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112944138335080853134995 3169416207502621279702493)
                ·
                  refine ⟨1188531077813482979888435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3169416207502621279702493 1188531077813482979888435)
                  ·
                    refine ⟨1782796616720224469832653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1188531077813482979888435 1782796616720224469832653)
                    ·
                      refine ⟨668548731270084176187245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1782796616720224469832653 668548731270084176187245)
                      ·
                        rfl

theorem cell23_1301994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_1301994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1301994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1301994 prefixEnd_1301994 := by exact prefixLift 1301994
  have htrace : WordTrace (prefixWord ++ tailWord_1301994) baseStart_1301994 baseEnd_1301994 := by
    simpa [prefixWord, tailWord_1301994, baseEnd_1301994] using wordTrace_append hprefix tailTrace_1301994
  have hstable : (prefixWord ++ tailWord_1301994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301994).length < 2 ^ (prefixWord ++ tailWord_1301994).sum := by decide
  have hdescent : baseEnd_1301994 < baseStart_1301994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302010 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_1302010 : Nat := 118140960795 + 1302010 * 2 ^ 59
def prefixEnd_1302010 : Nat := 4983230072969 + 3 ^ 40 * 1302010 * 2
def baseEnd_1302010 : Nat := 222852315653518704529057

theorem tailTrace_1302010 : CollatzResearch.WordTrace tailWord_1302010 prefixEnd_1302010 222852315653518704529057 := by
  unfold tailWord_1302010
  simp only [CollatzResearch.WordTrace]
  refine ⟨11872051503261902612419871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31658804008698406966452989 11872051503261902612419871)
  ·
    refine ⟨17808077254892853918629807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11872051503261902612419871 17808077254892853918629807)
    ·
      refine ⟨26712115882339280877944711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17808077254892853918629807 26712115882339280877944711)
      ·
        refine ⟨40068173823508921316917067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26712115882339280877944711 40068173823508921316917067)
        ·
          refine ⟨60102260735263381975375601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40068173823508921316917067 60102260735263381975375601)
          ·
            refine ⟨45076695551447536481531701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60102260735263381975375601 45076695551447536481531701)
            ·
              refine ⟨4225940207948206545143597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45076695551447536481531701 4225940207948206545143597)
              ·
                refine ⟨1584727577980577454428849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4225940207948206545143597 1584727577980577454428849)
                ·
                  refine ⟨1188545683485433090821637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584727577980577454428849 1188545683485433090821637)
                  ·
                    refine ⟨222852315653518704529057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1188545683485433090821637 222852315653518704529057)
                    ·
                      rfl

theorem cell23_1302010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_1302010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302010 prefixEnd_1302010 := by exact prefixLift 1302010
  have htrace : WordTrace (prefixWord ++ tailWord_1302010) baseStart_1302010 baseEnd_1302010 := by
    simpa [prefixWord, tailWord_1302010, baseEnd_1302010] using wordTrace_append hprefix tailTrace_1302010
  have hstable : (prefixWord ++ tailWord_1302010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302010).length < 2 ^ (prefixWord ++ tailWord_1302010).sum := by decide
  have hdescent : baseEnd_1302010 < baseStart_1302010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302013 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1302013 : Nat := 118140960795 + 1302013 * 2 ^ 59
def prefixEnd_1302013 : Nat := 4983230072969 + 3 ^ 40 * 1302013 * 2
def baseEnd_1302013 : Nat := 668558487402519601849657

theorem tailTrace_1302013 : CollatzResearch.WordTrace tailWord_1302013 prefixEnd_1302013 668558487402519601849657 := by
  unfold tailWord_1302013
  simp only [CollatzResearch.WordTrace]
  refine ⟨47488315432036741962038693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31658876954691161308025795 47488315432036741962038693)
  ·
    refine ⟨8904059143506889117882255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47488315432036741962038693 8904059143506889117882255)
    ·
      refine ⟨13356088715260333676823383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904059143506889117882255 13356088715260333676823383)
      ·
        refine ⟨20034133072890500515235075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13356088715260333676823383 20034133072890500515235075)
        ·
          refine ⟨30051199609335750772852613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20034133072890500515235075 30051199609335750772852613)
          ·
            refine ⟨5634599926750453269909865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30051199609335750772852613 5634599926750453269909865)
            ·
              refine ⟨4225949945062839952432399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634599926750453269909865 4225949945062839952432399)
              ·
                refine ⟨6338924917594259928648599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225949945062839952432399 6338924917594259928648599)
                ·
                  refine ⟨9508387376391389892972899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6338924917594259928648599 9508387376391389892972899)
                  ·
                    refine ⟨14262581064587084839459349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9508387376391389892972899 14262581064587084839459349)
                    ·
                      refine ⟨668558487402519601849657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14262581064587084839459349 668558487402519601849657)
                      ·
                        rfl

theorem cell23_1302013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1302013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302013 prefixEnd_1302013 := by exact prefixLift 1302013
  have htrace : WordTrace (prefixWord ++ tailWord_1302013) baseStart_1302013 baseEnd_1302013 := by
    simpa [prefixWord, tailWord_1302013, baseEnd_1302013] using wordTrace_append hprefix tailTrace_1302013
  have hstable : (prefixWord ++ tailWord_1302013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302013).length < 2 ^ (prefixWord ++ tailWord_1302013).sum := by decide
  have hdescent : baseEnd_1302013 < baseStart_1302013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302023 : List Nat := [1, 1, 4, 3, 2, 1, 2, 9]
def baseStart_1302023 : Nat := 118140960795 + 1302023 * 2 ^ 59
def prefixEnd_1302023 : Nat := 4983230072969 + 3 ^ 40 * 1302023 * 2
def baseEnd_1302023 : Nat := 24761615637372761582393

theorem tailTrace_1302023 : CollatzResearch.WordTrace tailWord_1302023 prefixEnd_1302023 24761615637372761582393 := by
  unfold tailWord_1302023
  simp only [CollatzResearch.WordTrace]
  refine ⟨47488680162000513669902723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31659120108000342446601815 47488680162000513669902723)
  ·
    refine ⟨71233020243000770504854085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47488680162000513669902723 71233020243000770504854085)
    ·
      refine ⟨13356191295562644469660141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71233020243000770504854085 13356191295562644469660141)
      ·
        refine ⟨5008571735835991676122553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13356191295562644469660141 5008571735835991676122553)
        ·
          refine ⟨3756428801876993757091915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5008571735835991676122553 3756428801876993757091915)
          ·
            refine ⟨5634643202815490635637873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756428801876993757091915 5634643202815490635637873)
            ·
              refine ⟨4225982402111617976728405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634643202815490635637873 4225982402111617976728405)
              ·
                refine ⟨24761615637372761582393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4225982402111617976728405 24761615637372761582393)
                ·
                  rfl

theorem cell23_1302023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 9].length) (baseStart_1302023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302023 prefixEnd_1302023 := by exact prefixLift 1302023
  have htrace : WordTrace (prefixWord ++ tailWord_1302023) baseStart_1302023 baseEnd_1302023 := by
    simpa [prefixWord, tailWord_1302023, baseEnd_1302023] using wordTrace_append hprefix tailTrace_1302023
  have hstable : (prefixWord ++ tailWord_1302023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302023).length < 2 ^ (prefixWord ++ tailWord_1302023).sum := by decide
  have hdescent : baseEnd_1302023 < baseStart_1302023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302051 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 1, 2, 2]
def baseStart_1302051 : Nat := 118140960795 + 1302051 * 2 ^ 59
def prefixEnd_1302051 : Nat := 4983230072969 + 3 ^ 40 * 1302051 * 2
def baseEnd_1302051 : Nat := 668577999667390453174483

theorem tailTrace_1302051 : CollatzResearch.WordTrace tailWord_1302051 prefixEnd_1302051 668577999667390453174483 := by
  unfold tailWord_1302051
  simp only [CollatzResearch.WordTrace]
  refine ⟨47489701405899074451922007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31659800937266049634614671 47489701405899074451922007)
  ·
    refine ⟨71234552108848611677883011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47489701405899074451922007 71234552108848611677883011)
    ·
      refine ⟨106851828163272917516824517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71234552108848611677883011 106851828163272917516824517)
      ·
        refine ⟨20034717780613672034404597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106851828163272917516824517 20034717780613672034404597)
        ·
          refine ⟨1878254791932531753225431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20034717780613672034404597 1878254791932531753225431)
          ·
            refine ⟨2817382187898797629838147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878254791932531753225431 2817382187898797629838147)
            ·
              refine ⟨4226073281848196444757221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817382187898797629838147 4226073281848196444757221)
              ·
                refine ⟨792388740346536833391979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4226073281848196444757221 792388740346536833391979)
                ·
                  refine ⟨1188583110519805250087969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792388740346536833391979 1188583110519805250087969)
                  ·
                    refine ⟨891437332889853937565977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188583110519805250087969 891437332889853937565977)
                    ·
                      refine ⟨668577999667390453174483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891437332889853937565977 668577999667390453174483)
                      ·
                        rfl

theorem cell23_1302051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_1302051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302051 prefixEnd_1302051 := by exact prefixLift 1302051
  have htrace : WordTrace (prefixWord ++ tailWord_1302051) baseStart_1302051 baseEnd_1302051 := by
    simpa [prefixWord, tailWord_1302051, baseEnd_1302051] using wordTrace_append hprefix tailTrace_1302051
  have hstable : (prefixWord ++ tailWord_1302051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302051).length < 2 ^ (prefixWord ++ tailWord_1302051).sum := by decide
  have hdescent : baseEnd_1302051 < baseStart_1302051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302067 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 3]
def baseStart_1302067 : Nat := 118140960795 + 1302067 * 2 ^ 59
def prefixEnd_1302067 : Nat := 4983230072969 + 3 ^ 40 * 1302067 * 2
def baseEnd_1302067 : Nat := 668586215357862390574409

theorem tailTrace_1302067 : CollatzResearch.WordTrace tailWord_1302067 prefixEnd_1302067 668586215357862390574409 := by
  unfold tailWord_1302067
  simp only [CollatzResearch.WordTrace]
  refine ⟨47490284973841109184504455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31660189982560739456336303 47490284973841109184504455)
  ·
    refine ⟨71235427460761663776756683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47490284973841109184504455 71235427460761663776756683)
    ·
      refine ⟨106853141191142495665135025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71235427460761663776756683 106853141191142495665135025)
      ·
        refine ⟨80139855893356871748851269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106853141191142495665135025 80139855893356871748851269)
        ·
          refine ⟨15026222980004413452909613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80139855893356871748851269 15026222980004413452909613)
          ·
            refine ⟨5634833617501655044841105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15026222980004413452909613 5634833617501655044841105)
            ·
              refine ⟨4226125213126241283630829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634833617501655044841105 4226125213126241283630829)
              ·
                refine ⟨1584796954922340481361561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4226125213126241283630829 1584796954922340481361561)
                ·
                  refine ⟨1188597716191755361021171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584796954922340481361561 1188597716191755361021171)
                  ·
                    refine ⟨1782896574287633041531757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1188597716191755361021171 1782896574287633041531757)
                    ·
                      refine ⟨668586215357862390574409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1782896574287633041531757 668586215357862390574409)
                      ·
                        rfl

theorem cell23_1302067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_1302067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302067 prefixEnd_1302067 := by exact prefixLift 1302067
  have htrace : WordTrace (prefixWord ++ tailWord_1302067) baseStart_1302067 baseEnd_1302067 := by
    simpa [prefixWord, tailWord_1302067, baseEnd_1302067] using wordTrace_append hprefix tailTrace_1302067
  have hstable : (prefixWord ++ tailWord_1302067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302067).length < 2 ^ (prefixWord ++ tailWord_1302067).sum := by decide
  have hdescent : baseEnd_1302067 < baseStart_1302067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302130 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 7]
def baseStart_1302130 : Nat := 118140960795 + 1302130 * 2 ^ 59
def prefixEnd_1302130 : Nat := 4983230072969 + 3 ^ 40 * 1302130 * 2
def baseEnd_1302130 : Nat := 74290951626566182676291

theorem tailTrace_1302130 : CollatzResearch.WordTrace tailWord_1302130 prefixEnd_1302130 74290951626566182676291 := by
  unfold tailWord_1302130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873145693153217736011961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31661721848408580629365229 11873145693153217736011961)
  ·
    refine ⟨8904859269864913302008971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11873145693153217736011961 8904859269864913302008971)
    ·
      refine ⟨13357288904797369953013457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904859269864913302008971 13357288904797369953013457)
      ·
        refine ⟨10017966678598027464760093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13357288904797369953013457 10017966678598027464760093)
        ·
          refine ⟨3756737504474260299285035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10017966678598027464760093 3756737504474260299285035)
          ·
            refine ⟨5635106256711390448927553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756737504474260299285035 5635106256711390448927553)
            ·
              refine ⟨4226329692533542836695665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5635106256711390448927553 4226329692533542836695665)
              ·
                refine ⟨3169747269400157127521749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226329692533542836695665 3169747269400157127521749)
                ·
                  refine ⟨74290951626566182676291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3169747269400157127521749 74290951626566182676291)
                  ·
                    rfl

theorem cell23_1302130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_1302130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302130 prefixEnd_1302130 := by exact prefixLift 1302130
  have htrace : WordTrace (prefixWord ++ tailWord_1302130) baseStart_1302130 baseEnd_1302130 := by
    simpa [prefixWord, tailWord_1302130, baseEnd_1302130] using wordTrace_append hprefix tailTrace_1302130
  have hstable : (prefixWord ++ tailWord_1302130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302130).length < 2 ^ (prefixWord ++ tailWord_1302130).sum := by decide
  have hdescent : baseEnd_1302130 < baseStart_1302130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302164 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 7]
def baseStart_1302164 : Nat := 118140960795 + 1302164 * 2 ^ 59
def prefixEnd_1302164 : Nat := 4983230072969 + 3 ^ 40 * 1302164 * 2
def baseEnd_1302164 : Nat := 74292891442372056784607

theorem tailTrace_1302164 : CollatzResearch.WordTrace tailWord_1302164 prefixEnd_1302164 74292891442372056784607 := by
  unfold tailWord_1302164
  simp only [CollatzResearch.WordTrace]
  refine ⟨23746911427244847375392773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31662548569659796500523697 23746911427244847375392773)
  ·
    refine ⟨4452545892608408882886145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23746911427244847375392773 4452545892608408882886145)
    ·
      refine ⟨3339409419456306662164609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4452545892608408882886145 3339409419456306662164609)
      ·
        refine ⟨2504557064592229996623457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3339409419456306662164609 2504557064592229996623457)
        ·
          refine ⟨1878417798444172497467593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504557064592229996623457 1878417798444172497467593)
          ·
            refine ⟨1408813348833129373100695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878417798444172497467593 1408813348833129373100695)
            ·
              refine ⟨2113220023249694059651043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408813348833129373100695 2113220023249694059651043)
              ·
                refine ⟨3169830034874541089476565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113220023249694059651043 3169830034874541089476565)
                ·
                  refine ⟨74292891442372056784607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3169830034874541089476565 74292891442372056784607)
                  ·
                    rfl

theorem cell23_1302164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_1302164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302164 prefixEnd_1302164 := by exact prefixLift 1302164
  have htrace : WordTrace (prefixWord ++ tailWord_1302164) baseStart_1302164 baseEnd_1302164 := by
    simpa [prefixWord, tailWord_1302164, baseEnd_1302164] using wordTrace_append hprefix tailTrace_1302164
  have hstable : (prefixWord ++ tailWord_1302164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302164).length < 2 ^ (prefixWord ++ tailWord_1302164).sum := by decide
  have hdescent : baseEnd_1302164 < baseStart_1302164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302175 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1302175 : Nat := 118140960795 + 1302175 * 2 ^ 59
def prefixEnd_1302175 : Nat := 4983230072969 + 3 ^ 40 * 1302175 * 2
def baseEnd_1302175 : Nat := 668641671268547968023913

theorem tailTrace_1302175 : CollatzResearch.WordTrace tailWord_1302175 prefixEnd_1302175 668641671268547968023913 := by
  unfold tailWord_1302175
  simp only [CollatzResearch.WordTrace]
  refine ⟨47494224057449843629435979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31662816038299895752957319 47494224057449843629435979)
  ·
    refine ⟨71241336086174765444153969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47494224057449843629435979 71241336086174765444153969)
    ·
      refine ⟨53431002064631074083115477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71241336086174765444153969 53431002064631074083115477)
      ·
        refine ⟨1252289110889790798823019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53431002064631074083115477 1252289110889790798823019)
        ·
          refine ⟨1878433666334686198234529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252289110889790798823019 1878433666334686198234529)
          ·
            refine ⟨1408825249751014648675897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878433666334686198234529 1408825249751014648675897)
            ·
              refine ⟨1056618937313260986506923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408825249751014648675897 1056618937313260986506923)
              ·
                refine ⟨1584928405969891479760385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056618937313260986506923 1584928405969891479760385)
                ·
                  refine ⟨1188696304477418609820289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584928405969891479760385 1188696304477418609820289)
                  ·
                    refine ⟨891522228358063957365217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188696304477418609820289 891522228358063957365217)
                    ·
                      refine ⟨668641671268547968023913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891522228358063957365217 668641671268547968023913)
                      ·
                        rfl

theorem cell23_1302175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1302175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302175 prefixEnd_1302175 := by exact prefixLift 1302175
  have htrace : WordTrace (prefixWord ++ tailWord_1302175) baseStart_1302175 baseEnd_1302175 := by
    simpa [prefixWord, tailWord_1302175, baseEnd_1302175] using wordTrace_append hprefix tailTrace_1302175
  have hstable : (prefixWord ++ tailWord_1302175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302175).length < 2 ^ (prefixWord ++ tailWord_1302175).sum := by decide
  have hdescent : baseEnd_1302175 < baseStart_1302175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302200 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_1302200 : Nat := 118140960795 + 1302200 * 2 ^ 59
def prefixEnd_1302200 : Nat := 4983230072969 + 3 ^ 40 * 1302200 * 2
def baseEnd_1302200 : Nat := 668654508284910370211297

theorem tailTrace_1302200 : CollatzResearch.WordTrace tailWord_1302200 prefixEnd_1302200 668654508284910370211297 := by
  unfold tailWord_1302200
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747567941179636449548027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31663423921572848599397369 23747567941179636449548027)
  ·
    refine ⟨35621351911769454674322041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23747567941179636449548027 35621351911769454674322041)
    ·
      refine ⟨26716013933827091005741531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35621351911769454674322041 26716013933827091005741531)
      ·
        refine ⟨40074020900740636508612297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26716013933827091005741531 40074020900740636508612297)
        ·
          refine ⟨30055515675555477381459223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40074020900740636508612297 30055515675555477381459223)
          ·
            refine ⟨45083273513333216072188835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30055515675555477381459223 45083273513333216072188835)
            ·
              refine ⟨67624910269999824108283253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45083273513333216072188835 67624910269999824108283253)
              ·
                refine ⟨6339835337812483510151555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67624910269999824108283253 6339835337812483510151555)
                ·
                  refine ⟨9509753006718725265227333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6339835337812483510151555 9509753006718725265227333)
                  ·
                    refine ⟨1783078688759760987230125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9509753006718725265227333 1783078688759760987230125)
                    ·
                      refine ⟨668654508284910370211297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1783078688759760987230125 668654508284910370211297)
                      ·
                        rfl

theorem cell23_1302200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_1302200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302200 prefixEnd_1302200 := by exact prefixLift 1302200
  have htrace : WordTrace (prefixWord ++ tailWord_1302200) baseStart_1302200 baseEnd_1302200 := by
    simpa [prefixWord, tailWord_1302200, baseEnd_1302200] using wordTrace_append hprefix tailTrace_1302200
  have hstable : (prefixWord ++ tailWord_1302200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302200).length < 2 ^ (prefixWord ++ tailWord_1302200).sum := by decide
  have hdescent : baseEnd_1302200 < baseStart_1302200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302203 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 10]
def baseStart_1302203 : Nat := 118140960795 + 1302203 * 2 ^ 59
def prefixEnd_1302203 : Nat := 4983230072969 + 3 ^ 40 * 1302203 * 2
def baseEnd_1302203 : Nat := 74295116525208206497087

theorem tailTrace_1302203 : CollatzResearch.WordTrace tailWord_1302203 prefixEnd_1302203 74295116525208206497087 := by
  unfold tailWord_1302203
  simp only [CollatzResearch.WordTrace]
  refine ⟨47495245301348404411455263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31663496867565602940970175 47495245301348404411455263)
  ·
    refine ⟨71242867952022606617182895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47495245301348404411455263 71242867952022606617182895)
    ·
      refine ⟨106864301928033909925774343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71242867952022606617182895 106864301928033909925774343)
      ·
        refine ⟨160296452892050864888661515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106864301928033909925774343 160296452892050864888661515)
        ·
          refine ⟨240444679338076297332992273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160296452892050864888661515 240444679338076297332992273)
          ·
            refine ⟨180333509503557222999744205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240444679338076297332992273 180333509503557222999744205)
            ·
              refine ⟨67625066063833958624904077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180333509503557222999744205 67625066063833958624904077)
              ·
                refine ⟨25359399773937734484339029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67625066063833958624904077 25359399773937734484339029)
                ·
                  refine ⟨74295116525208206497087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 25359399773937734484339029 74295116525208206497087)
                  ·
                    rfl

theorem cell23_1302203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 10].length) (baseStart_1302203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302203 prefixEnd_1302203 := by exact prefixLift 1302203
  have htrace : WordTrace (prefixWord ++ tailWord_1302203) baseStart_1302203 baseEnd_1302203 := by
    simpa [prefixWord, tailWord_1302203, baseEnd_1302203] using wordTrace_append hprefix tailTrace_1302203
  have hstable : (prefixWord ++ tailWord_1302203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302203).length < 2 ^ (prefixWord ++ tailWord_1302203).sum := by decide
  have hdescent : baseEnd_1302203 < baseStart_1302203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302304 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1302304 : Nat := 118140960795 + 1302304 * 2 ^ 59
def prefixEnd_1302304 : Nat := 4983230072969 + 3 ^ 40 * 1302304 * 2
def baseEnd_1302304 : Nat := 668707910272977963310819

theorem tailTrace_1302304 : CollatzResearch.WordTrace tailWord_1302304 prefixEnd_1302304 668707910272977963310819 := by
  unfold tailWord_1302304
  simp only [CollatzResearch.WordTrace]
  refine ⟨23749464536991249330440983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31665952715988332440587977 23749464536991249330440983)
  ·
    refine ⟨35624196805486873995661475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23749464536991249330440983 35624196805486873995661475)
    ·
      refine ⟨53436295208230310993492213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35624196805486873995661475 53436295208230310993492213)
      ·
        refine ⟨5009652675771591655639895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53436295208230310993492213 5009652675771591655639895)
        ·
          refine ⟨7514479013657387483459843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009652675771591655639895 7514479013657387483459843)
          ·
            refine ⟨11271718520486081225189765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7514479013657387483459843 11271718520486081225189765)
            ·
              refine ⟨2113447222591140229723081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11271718520486081225189765 2113447222591140229723081)
              ·
                refine ⟨1585085416943355172292311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113447222591140229723081 1585085416943355172292311)
                ·
                  refine ⟨2377628125415032758438467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585085416943355172292311 2377628125415032758438467)
                  ·
                    refine ⟨3566442188122549137657701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2377628125415032758438467 3566442188122549137657701)
                    ·
                      refine ⟨668707910272977963310819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3566442188122549137657701 668707910272977963310819)
                      ·
                        rfl

theorem cell23_1302304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1302304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302304 prefixEnd_1302304 := by exact prefixLift 1302304
  have htrace : WordTrace (prefixWord ++ tailWord_1302304) baseStart_1302304 baseEnd_1302304 := by
    simpa [prefixWord, tailWord_1302304, baseEnd_1302304] using wordTrace_append hprefix tailTrace_1302304
  have hstable : (prefixWord ++ tailWord_1302304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302304).length < 2 ^ (prefixWord ++ tailWord_1302304).sum := by decide
  have hdescent : baseEnd_1302304 < baseStart_1302304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302307 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 3]
def baseStart_1302307 : Nat := 118140960795 + 1302307 * 2 ^ 59
def prefixEnd_1302307 : Nat := 4983230072969 + 3 ^ 40 * 1302307 * 2
def baseEnd_1302307 : Nat := 668709450714941451573305

theorem tailTrace_1302307 : CollatzResearch.WordTrace tailWord_1302307 prefixEnd_1302307 668709450714941451573305 := by
  unfold tailWord_1302307
  simp only [CollatzResearch.WordTrace]
  refine ⟨47499038492971630173241175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31666025661981086782160783 47499038492971630173241175)
  ·
    refine ⟨71248557739457445259861763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47499038492971630173241175 71248557739457445259861763)
    ·
      refine ⟨106872836609186167889792645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71248557739457445259861763 106872836609186167889792645)
      ·
        refine ⟨20038656864222406479336121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106872836609186167889792645 20038656864222406479336121)
        ·
          refine ⟨15028992648166804859502091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20038656864222406479336121 15028992648166804859502091)
          ·
            refine ⟨22543488972250207289253137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15028992648166804859502091 22543488972250207289253137)
            ·
              refine ⟨16907616729187655466939853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22543488972250207289253137 16907616729187655466939853)
              ·
                refine ⟨6340356273445370800102445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16907616729187655466939853 6340356273445370800102445)
                ·
                  refine ⟨2377633602542014050038417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6340356273445370800102445 2377633602542014050038417)
                  ·
                    refine ⟨1783225201906510537528813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2377633602542014050038417 1783225201906510537528813)
                    ·
                      refine ⟨668709450714941451573305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1783225201906510537528813 668709450714941451573305)
                      ·
                        rfl

theorem cell23_1302307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_1302307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302307 prefixEnd_1302307 := by exact prefixLift 1302307
  have htrace : WordTrace (prefixWord ++ tailWord_1302307) baseStart_1302307 baseEnd_1302307 := by
    simpa [prefixWord, tailWord_1302307, baseEnd_1302307] using wordTrace_append hprefix tailTrace_1302307
  have hstable : (prefixWord ++ tailWord_1302307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302307).length < 2 ^ (prefixWord ++ tailWord_1302307).sum := by decide
  have hdescent : baseEnd_1302307 < baseStart_1302307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302324 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1302324 : Nat := 118140960795 + 1302324 * 2 ^ 59
def prefixEnd_1302324 : Nat := 4983230072969 + 3 ^ 40 * 1302324 * 2
def baseEnd_1302324 : Nat := 668718179886067885060727

theorem tailTrace_1302324 : CollatzResearch.WordTrace tailWord_1302324 prefixEnd_1302324 668718179886067885060727 := by
  unfold tailWord_1302324
  simp only [CollatzResearch.WordTrace]
  refine ⟨23749829266955021038305013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31666439022606694717740017 23749829266955021038305013)
  ·
    refine ⟨2226546493777033222341095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23749829266955021038305013 2226546493777033222341095)
    ·
      refine ⟨3339819740665549833511643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2226546493777033222341095 3339819740665549833511643)
      ·
        refine ⟨5009729610998324750267465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339819740665549833511643 5009729610998324750267465)
        ·
          refine ⟨3757297208248743562700599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5009729610998324750267465 3757297208248743562700599)
          ·
            refine ⟨5635945812373115344050899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757297208248743562700599 5635945812373115344050899)
            ·
              refine ⟨8453918718559673016076349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635945812373115344050899 8453918718559673016076349)
              ·
                refine ⟨3170219519459877381028631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8453918718559673016076349 3170219519459877381028631)
                ·
                  refine ⟨4755329279189816071542947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170219519459877381028631 4755329279189816071542947)
                  ·
                    refine ⟨7132993918784724107314421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4755329279189816071542947 7132993918784724107314421)
                    ·
                      refine ⟨668718179886067885060727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7132993918784724107314421 668718179886067885060727)
                      ·
                        rfl

theorem cell23_1302324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1302324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302324 prefixEnd_1302324 := by exact prefixLift 1302324
  have htrace : WordTrace (prefixWord ++ tailWord_1302324) baseStart_1302324 baseEnd_1302324 := by
    simpa [prefixWord, tailWord_1302324, baseEnd_1302324] using wordTrace_append hprefix tailTrace_1302324
  have hstable : (prefixWord ++ tailWord_1302324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302324).length < 2 ^ (prefixWord ++ tailWord_1302324).sum := by decide
  have hdescent : baseEnd_1302324 < baseStart_1302324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302348 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_1302348 : Nat := 118140960795 + 1302348 * 2 ^ 59
def prefixEnd_1302348 : Nat := 4983230072969 + 3 ^ 40 * 1302348 * 2
def baseEnd_1302348 : Nat := 222910167807258597053539

theorem tailTrace_1302348 : CollatzResearch.WordTrace tailWord_1302348 prefixEnd_1302348 222910167807258597053539 := by
  unfold tailWord_1302348
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750266942911547087741849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31667022590548729450322465 23750266942911547087741849)
  ·
    refine ⟨17812700207183660315806387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23750266942911547087741849 17812700207183660315806387)
    ·
      refine ⟨26719050310775490473709581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17812700207183660315806387 26719050310775490473709581)
      ·
        refine ⟨10019643866540808927641093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26719050310775490473709581 10019643866540808927641093)
        ·
          refine ⟨1878683224976401673932705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10019643866540808927641093 1878683224976401673932705)
          ·
            refine ⟨1409012418732301255449529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1878683224976401673932705 1409012418732301255449529)
            ·
              refine ⟨1056759314049225941587147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409012418732301255449529 1056759314049225941587147)
              ·
                refine ⟨1585138971073838912380721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056759314049225941587147 1585138971073838912380721)
                ·
                  refine ⟨1188854228305379184285541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1585138971073838912380721 1188854228305379184285541)
                  ·
                    refine ⟨222910167807258597053539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1188854228305379184285541 222910167807258597053539)
                    ·
                      rfl

theorem cell23_1302348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_1302348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302348 prefixEnd_1302348 := by exact prefixLift 1302348
  have htrace : WordTrace (prefixWord ++ tailWord_1302348) baseStart_1302348 baseEnd_1302348 := by
    simpa [prefixWord, tailWord_1302348, baseEnd_1302348] using wordTrace_append hprefix tailTrace_1302348
  have hstable : (prefixWord ++ tailWord_1302348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302348).length < 2 ^ (prefixWord ++ tailWord_1302348).sum := by decide
  have hdescent : baseEnd_1302348 < baseStart_1302348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302360 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1302360 : Nat := 118140960795 + 1302360 * 2 ^ 59
def prefixEnd_1302360 : Nat := 4983230072969 + 3 ^ 40 * 1302360 * 2
def baseEnd_1302360 : Nat := 668736665189629744210561

theorem tailTrace_1302360 : CollatzResearch.WordTrace tailWord_1302360 prefixEnd_1302360 668736665189629744210561 := by
  unfold tailWord_1302360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23750485780889810112460267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31667314374519746816613689 23750485780889810112460267)
  ·
    refine ⟨35625728671334715168690401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23750485780889810112460267 35625728671334715168690401)
    ·
      refine ⟨26719296503501036376517801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35625728671334715168690401 26719296503501036376517801)
      ·
        refine ⟨20039472377625777282388351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26719296503501036376517801 20039472377625777282388351)
        ·
          refine ⟨30059208566438665923582527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20039472377625777282388351 30059208566438665923582527)
          ·
            refine ⟨45088812849657998885373791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30059208566438665923582527 45088812849657998885373791)
            ·
              refine ⟨67633219274486998328060687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45088812849657998885373791 67633219274486998328060687)
              ·
                refine ⟨101449828911730497492091031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67633219274486998328060687 101449828911730497492091031)
                ·
                  refine ⟨152174743367595746238136547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101449828911730497492091031 152174743367595746238136547)
                  ·
                    refine ⟨228262115051393619357204821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 152174743367595746238136547 228262115051393619357204821)
                    ·
                      refine ⟨668736665189629744210561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 228262115051393619357204821 668736665189629744210561)
                      ·
                        rfl

theorem cell23_1302360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1302360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302360 prefixEnd_1302360 := by exact prefixLift 1302360
  have htrace : WordTrace (prefixWord ++ tailWord_1302360) baseStart_1302360 baseEnd_1302360 := by
    simpa [prefixWord, tailWord_1302360, baseEnd_1302360] using wordTrace_append hprefix tailTrace_1302360
  have hstable : (prefixWord ++ tailWord_1302360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302360).length < 2 ^ (prefixWord ++ tailWord_1302360).sum := by decide
  have hdescent : baseEnd_1302360 < baseStart_1302360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302381 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1302381 : Nat := 118140960795 + 1302381 * 2 ^ 59
def prefixEnd_1302381 : Nat := 4983230072969 + 3 ^ 40 * 1302381 * 2
def baseEnd_1302381 : Nat := 668747448283374162047965

theorem tailTrace_1302381 : CollatzResearch.WordTrace tailWord_1302381 prefixEnd_1302381 668747448283374162047965 := by
  unfold tailWord_1302381
  simp only [CollatzResearch.WordTrace]
  refine ⟨47501737494703540811434997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31667824996469027207623331 47501737494703540811434997)
  ·
    refine ⟨4453287890128456951072031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47501737494703540811434997 4453287890128456951072031)
    ·
      refine ⟨6679931835192685426608047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4453287890128456951072031 6679931835192685426608047)
      ·
        refine ⟨10019897752789028139912071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6679931835192685426608047 10019897752789028139912071)
        ·
          refine ⟨15029846629183542209868107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10019897752789028139912071 15029846629183542209868107)
          ·
            refine ⟨22544769943775313314802161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15029846629183542209868107 22544769943775313314802161)
            ·
              refine ⟨16908577457831484986101621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22544769943775313314802161 16908577457831484986101621)
              ·
                refine ⟨1585179136671701717447027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16908577457831484986101621 1585179136671701717447027)
                ·
                  refine ⟨2377768705007552576170541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585179136671701717447027 2377768705007552576170541)
                  ·
                    refine ⟨891663264377832216063953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377768705007552576170541 891663264377832216063953)
                    ·
                      refine ⟨668747448283374162047965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891663264377832216063953 668747448283374162047965)
                      ·
                        rfl

theorem cell23_1302381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1302381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302381 prefixEnd_1302381 := by exact prefixLift 1302381
  have htrace : WordTrace (prefixWord ++ tailWord_1302381) baseStart_1302381 baseEnd_1302381 := by
    simpa [prefixWord, tailWord_1302381, baseEnd_1302381] using wordTrace_append hprefix tailTrace_1302381
  have hstable : (prefixWord ++ tailWord_1302381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302381).length < 2 ^ (prefixWord ++ tailWord_1302381).sum := by decide
  have hdescent : baseEnd_1302381 < baseStart_1302381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302398 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1302398 : Nat := 118140960795 + 1302398 * 2 ^ 59
def prefixEnd_1302398 : Nat := 4983230072969 + 3 ^ 40 * 1302398 * 2
def baseEnd_1302398 : Nat := 668756177454500595535387

theorem tailTrace_1302398 : CollatzResearch.WordTrace tailWord_1302398 prefixEnd_1302398 668756177454500595535387 := by
  unfold tailWord_1302398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937794691955244089350481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31668238357094635143202565 5937794691955244089350481)
  ·
    refine ⟨4453346018966433067012861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5937794691955244089350481 4453346018966433067012861)
    ·
      refine ⟨1670004757112412400129823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4453346018966433067012861 1670004757112412400129823)
      ·
        refine ⟨2505007135668618600194735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670004757112412400129823 2505007135668618600194735)
        ·
          refine ⟨3757510703502927900292103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505007135668618600194735 3757510703502927900292103)
          ·
            refine ⟨5636266055254391850438155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757510703502927900292103 5636266055254391850438155)
            ·
              refine ⟨8454399082881587775657233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636266055254391850438155 8454399082881587775657233)
              ·
                refine ⟨6340799312161190831742925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8454399082881587775657233 6340799312161190831742925)
                ·
                  refine ⟨2377799742060446561903597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6340799312161190831742925 2377799742060446561903597)
                  ·
                    refine ⟨891674903272667460713849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377799742060446561903597 891674903272667460713849)
                    ·
                      refine ⟨668756177454500595535387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891674903272667460713849 668756177454500595535387)
                      ·
                        rfl

theorem cell23_1302398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1302398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302398 prefixEnd_1302398 := by exact prefixLift 1302398
  have htrace : WordTrace (prefixWord ++ tailWord_1302398) baseStart_1302398 baseEnd_1302398 := by
    simpa [prefixWord, tailWord_1302398, baseEnd_1302398] using wordTrace_append hprefix tailTrace_1302398
  have hstable : (prefixWord ++ tailWord_1302398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302398).length < 2 ^ (prefixWord ++ tailWord_1302398).sum := by decide
  have hdescent : baseEnd_1302398 < baseStart_1302398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302447 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 4, 5]
def baseStart_1302447 : Nat := 118140960795 + 1302447 * 2 ^ 59
def prefixEnd_1302447 : Nat := 4983230072969 + 3 ^ 40 * 1302447 * 2
def baseEnd_1302447 : Nat := 222927112668856967940887

theorem tailTrace_1302447 : CollatzResearch.WordTrace tailWord_1302447 prefixEnd_1302447 222927112668856967940887 := by
  unfold tailWord_1302447
  simp only [CollatzResearch.WordTrace]
  refine ⟨47504144712464434083337595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31669429808309622722225063 47504144712464434083337595)
  ·
    refine ⟨71256217068696651125006393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47504144712464434083337595 71256217068696651125006393)
    ·
      refine ⟨53442162801522488343754795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71256217068696651125006393 53442162801522488343754795)
      ·
        refine ⟨80163244202283732515632193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53442162801522488343754795 80163244202283732515632193)
        ·
          refine ⟨60122433151712799386724145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80163244202283732515632193 60122433151712799386724145)
          ·
            refine ⟨45091824863784599540043109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60122433151712799386724145 45091824863784599540043109)
            ·
              refine ⟨8454717161959612413758083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45091824863784599540043109 8454717161959612413758083)
              ·
                refine ⟨12682075742939418620637125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454717161959612413758083 12682075742939418620637125)
                ·
                  refine ⟨2377889201801140991369461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12682075742939418620637125 2377889201801140991369461)
                  ·
                    refine ⟨222927112668856967940887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2377889201801140991369461 222927112668856967940887)
                    ·
                      rfl

theorem cell23_1302447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_1302447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302447 prefixEnd_1302447 := by exact prefixLift 1302447
  have htrace : WordTrace (prefixWord ++ tailWord_1302447) baseStart_1302447 baseEnd_1302447 := by
    simpa [prefixWord, tailWord_1302447, baseEnd_1302447] using wordTrace_append hprefix tailTrace_1302447
  have hstable : (prefixWord ++ tailWord_1302447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302447).length < 2 ^ (prefixWord ++ tailWord_1302447).sum := by decide
  have hdescent : baseEnd_1302447 < baseStart_1302447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302457 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1302457 : Nat := 118140960795 + 1302457 * 2 ^ 59
def prefixEnd_1302457 : Nat := 4983230072969 + 3 ^ 40 * 1302457 * 2
def baseEnd_1302457 : Nat := 668786472813115864697615

theorem tailTrace_1302457 : CollatzResearch.WordTrace tailWord_1302457 prefixEnd_1302457 668786472813115864697615 := by
  unfold tailWord_1302457
  simp only [CollatzResearch.WordTrace]
  refine ⟨47504509442428205791201625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31669672961618803860801083 47504509442428205791201625)
  ·
    refine ⟨35628382081821154343401219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47504509442428205791201625 35628382081821154343401219)
    ·
      refine ⟨53442573122731731515101829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35628382081821154343401219 53442573122731731515101829)
      ·
        refine ⟨10020482460512199659081593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53442573122731731515101829 10020482460512199659081593)
        ·
          refine ⟨7515361845384149744311195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10020482460512199659081593 7515361845384149744311195)
          ·
            refine ⟨11273042768076224616466793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515361845384149744311195 11273042768076224616466793)
            ·
              refine ⟨8454782076057168462350095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11273042768076224616466793 8454782076057168462350095)
              ·
                refine ⟨12682173114085752693525143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454782076057168462350095 12682173114085752693525143)
                ·
                  refine ⟨19023259671128629040287715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12682173114085752693525143 19023259671128629040287715)
                  ·
                    refine ⟨28534889506692943560431573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19023259671128629040287715 28534889506692943560431573)
                    ·
                      refine ⟨668786472813115864697615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28534889506692943560431573 668786472813115864697615)
                      ·
                        rfl

theorem cell23_1302457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1302457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302457 prefixEnd_1302457 := by exact prefixLift 1302457
  have htrace : WordTrace (prefixWord ++ tailWord_1302457) baseStart_1302457 baseEnd_1302457 := by
    simpa [prefixWord, tailWord_1302457, baseEnd_1302457] using wordTrace_append hprefix tailTrace_1302457
  have hstable : (prefixWord ++ tailWord_1302457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302457).length < 2 ^ (prefixWord ++ tailWord_1302457).sum := by decide
  have hdescent : baseEnd_1302457 < baseStart_1302457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302484 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1302484 : Nat := 118140960795 + 1302484 * 2 ^ 59
def prefixEnd_1302484 : Nat := 4983230072969 + 3 ^ 40 * 1302484 * 2
def baseEnd_1302484 : Nat := 668800336790787259059991

theorem tailTrace_1302484 : CollatzResearch.WordTrace tailWord_1302484 prefixEnd_1302484 668800336790787259059991 := by
  unfold tailWord_1302484
  simp only [CollatzResearch.WordTrace]
  refine ⟨23752747106665194701217253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31670329475553592934956337 23752747106665194701217253)
  ·
    refine ⟨4453640082499724006478235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23752747106665194701217253 4453640082499724006478235)
    ·
      refine ⟨6680460123749586009717353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4453640082499724006478235 6680460123749586009717353)
      ·
        refine ⟨5010345092812189507288015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6680460123749586009717353 5010345092812189507288015)
        ·
          refine ⟨7515517639218284260932023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010345092812189507288015 7515517639218284260932023)
          ·
            refine ⟨11273276458827426391398035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515517639218284260932023 11273276458827426391398035)
            ·
              refine ⟨16909914688241139587097053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11273276458827426391398035 16909914688241139587097053)
              ·
                refine ⟨6341218008090427345161395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16909914688241139587097053 6341218008090427345161395)
                ·
                  refine ⟨9511827012135641017742093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6341218008090427345161395 9511827012135641017742093)
                  ·
                    refine ⟨3566935129550865381653285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9511827012135641017742093 3566935129550865381653285)
                    ·
                      refine ⟨668800336790787259059991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3566935129550865381653285 668800336790787259059991)
                      ·
                        rfl

theorem cell23_1302484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1302484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302484 prefixEnd_1302484 := by exact prefixLift 1302484
  have htrace : WordTrace (prefixWord ++ tailWord_1302484) baseStart_1302484 baseEnd_1302484 := by
    simpa [prefixWord, tailWord_1302484, baseEnd_1302484] using wordTrace_append hprefix tailTrace_1302484
  have hstable : (prefixWord ++ tailWord_1302484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302484).length < 2 ^ (prefixWord ++ tailWord_1302484).sum := by decide
  have hdescent : baseEnd_1302484 < baseStart_1302484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302497 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_1302497 : Nat := 118140960795 + 1302497 * 2 ^ 59
def prefixEnd_1302497 : Nat := 4983230072969 + 3 ^ 40 * 1302497 * 2
def baseEnd_1302497 : Nat := 668807012039295708197431

theorem tailTrace_1302497 : CollatzResearch.WordTrace tailWord_1302497 prefixEnd_1302497 668807012039295708197431 := by
  unfold tailWord_1302497
  simp only [CollatzResearch.WordTrace]
  refine ⟨47505968362283292622657745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31670645574855528415105163 47505968362283292622657745)
  ·
    refine ⟨35629476271712469466993309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47505968362283292622657745 35629476271712469466993309)
    ·
      refine ⟨13361053601892176050122491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35629476271712469466993309 13361053601892176050122491)
      ·
        refine ⟨20041580402838264075183737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13361053601892176050122491 20041580402838264075183737)
        ·
          refine ⟨15031185302128698056387803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20041580402838264075183737 15031185302128698056387803)
          ·
            refine ⟨22546777953193047084581705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15031185302128698056387803 22546777953193047084581705)
            ·
              refine ⟨16910083464894785313436279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22546777953193047084581705 16910083464894785313436279)
              ·
                refine ⟨25365125197342177970154419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16910083464894785313436279 25365125197342177970154419)
                ·
                  refine ⟨38047687796013266955231629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25365125197342177970154419 38047687796013266955231629)
                  ·
                    refine ⟨14267882923504975108211861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38047687796013266955231629 14267882923504975108211861)
                    ·
                      refine ⟨668807012039295708197431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14267882923504975108211861 668807012039295708197431)
                      ·
                        rfl

theorem cell23_1302497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_1302497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302497 prefixEnd_1302497 := by exact prefixLift 1302497
  have htrace : WordTrace (prefixWord ++ tailWord_1302497) baseStart_1302497 baseEnd_1302497 := by
    simpa [prefixWord, tailWord_1302497, baseEnd_1302497] using wordTrace_append hprefix tailTrace_1302497
  have hstable : (prefixWord ++ tailWord_1302497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302497).length < 2 ^ (prefixWord ++ tailWord_1302497).sum := by decide
  have hdescent : baseEnd_1302497 < baseStart_1302497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302498 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1302498 : Nat := 118140960795 + 1302498 * 2 ^ 59
def prefixEnd_1302498 : Nat := 4983230072969 + 3 ^ 40 * 1302498 * 2
def baseEnd_1302498 : Nat := 222935841839983401428309

theorem tailTrace_1302498 : CollatzResearch.WordTrace tailWord_1302498 prefixEnd_1302498 222935841839983401428309 := by
  unfold tailWord_1302498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11876501208819917448361037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31670669890186446528962765 11876501208819917448361037)
  ·
    refine ⟨4453687953307469043135389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11876501208819917448361037 4453687953307469043135389)
    ·
      refine ⟨1670132982490300891175771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4453687953307469043135389 1670132982490300891175771)
      ·
        refine ⟨2505199473735451336763657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670132982490300891175771 2505199473735451336763657)
        ·
          refine ⟨1878899605301588502572743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2505199473735451336763657 1878899605301588502572743)
          ·
            refine ⟨2818349407952382753859115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878899605301588502572743 2818349407952382753859115)
            ·
              refine ⟨4227524111928574130788673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818349407952382753859115 4227524111928574130788673)
              ·
                refine ⟨3170643083946430598091505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4227524111928574130788673 3170643083946430598091505)
                ·
                  refine ⟨2377982312959822948568629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3170643083946430598091505 2377982312959822948568629)
                  ·
                    refine ⟨222935841839983401428309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2377982312959822948568629 222935841839983401428309)
                    ·
                      rfl

theorem cell23_1302498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1302498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302498 prefixEnd_1302498 := by exact prefixLift 1302498
  have htrace : WordTrace (prefixWord ++ tailWord_1302498) baseStart_1302498 baseEnd_1302498 := by
    simpa [prefixWord, tailWord_1302498, baseEnd_1302498] using wordTrace_append hprefix tailTrace_1302498
  have hstable : (prefixWord ++ tailWord_1302498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302498).length < 2 ^ (prefixWord ++ tailWord_1302498).sum := by decide
  have hdescent : baseEnd_1302498 < baseStart_1302498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302524 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 6]
def baseStart_1302524 : Nat := 118140960795 + 1302524 * 2 ^ 59
def prefixEnd_1302524 : Nat := 4983230072969 + 3 ^ 40 * 1302524 * 2
def baseEnd_1302524 : Nat := 74313430668551900284423

theorem tailTrace_1302524 : CollatzResearch.WordTrace tailWord_1302524 prefixEnd_1302524 74313430668551900284423 := by
  unfold tailWord_1302524
  simp only [CollatzResearch.WordTrace]
  refine ⟨23753476566592738116945313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31671302088790317489260417 23753476566592738116945313)
  ·
    refine ⟨17815107424944553587708985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23753476566592738116945313 17815107424944553587708985)
    ·
      refine ⟨13361330568708415190781739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17815107424944553587708985 13361330568708415190781739)
      ·
        refine ⟨20041995853062622786172609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13361330568708415190781739 20041995853062622786172609)
        ·
          refine ⟨15031496889796967089629457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20041995853062622786172609 15031496889796967089629457)
          ·
            refine ⟨11273622667347725317222093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15031496889796967089629457 11273622667347725317222093)
            ·
              refine ⟨4227608500255396993958285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11273622667347725317222093 4227608500255396993958285)
              ·
                refine ⟨1585353187595773872734357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4227608500255396993958285 1585353187595773872734357)
                ·
                  refine ⟨74313430668551900284423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1585353187595773872734357 74313430668551900284423)
                  ·
                    rfl

theorem cell23_1302524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_1302524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302524 prefixEnd_1302524 := by exact prefixLift 1302524
  have htrace : WordTrace (prefixWord ++ tailWord_1302524) baseStart_1302524 baseEnd_1302524 := by
    simpa [prefixWord, tailWord_1302524, baseEnd_1302524] using wordTrace_append hprefix tailTrace_1302524
  have hstable : (prefixWord ++ tailWord_1302524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302524).length < 2 ^ (prefixWord ++ tailWord_1302524).sum := by decide
  have hdescent : baseEnd_1302524 < baseStart_1302524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302527 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1302527 : Nat := 118140960795 + 1302527 * 2 ^ 59
def prefixEnd_1302527 : Nat := 4983230072969 + 3 ^ 40 * 1302527 * 2
def baseEnd_1302527 : Nat := 668822416458930590822293

theorem tailTrace_1302527 : CollatzResearch.WordTrace tailWord_1302527 prefixEnd_1302527 668822416458930590822293 := by
  unfold tailWord_1302527
  simp only [CollatzResearch.WordTrace]
  refine ⟨47507062552174607746249835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31671375034783071830833223 47507062552174607746249835)
  ·
    refine ⟨71260593828261911619374753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47507062552174607746249835 71260593828261911619374753)
    ·
      refine ⟨53445445371196433714531065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71260593828261911619374753 53445445371196433714531065)
      ·
        refine ⟨40084084028397325285898299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53445445371196433714531065 40084084028397325285898299)
        ·
          refine ⟨60126126042595987928847449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40084084028397325285898299 60126126042595987928847449)
          ·
            refine ⟨45094594531946990946635587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60126126042595987928847449 45094594531946990946635587)
            ·
              refine ⟨67641891797920486419953381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45094594531946990946635587 67641891797920486419953381)
              ·
                refine ⟨12682854712110091203741259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67641891797920486419953381 12682854712110091203741259)
                ·
                  refine ⟨19024282068165136805611889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12682854712110091203741259 19024282068165136805611889)
                  ·
                    refine ⟨14268211551123852604208917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19024282068165136805611889 14268211551123852604208917)
                    ·
                      refine ⟨668822416458930590822293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14268211551123852604208917 668822416458930590822293)
                      ·
                        rfl

theorem cell23_1302527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1302527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302527 prefixEnd_1302527 := by exact prefixLift 1302527
  have htrace : WordTrace (prefixWord ++ tailWord_1302527) baseStart_1302527 baseEnd_1302527 := by
    simpa [prefixWord, tailWord_1302527, baseEnd_1302527] using wordTrace_append hprefix tailTrace_1302527
  have hstable : (prefixWord ++ tailWord_1302527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302527).length < 2 ^ (prefixWord ++ tailWord_1302527).sum := by decide
  have hdescent : baseEnd_1302527 < baseStart_1302527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302538 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1302538 : Nat := 118140960795 + 1302538 * 2 ^ 59
def prefixEnd_1302538 : Nat := 4983230072969 + 3 ^ 40 * 1302538 * 2
def baseEnd_1302538 : Nat := 668828064746130047784743

theorem tailTrace_1302538 : CollatzResearch.WordTrace tailWord_1302538 prefixEnd_1302538 668828064746130047784743 := by
  unfold tailWord_1302538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11876865938783689156225067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31671642503423171083266845 11876865938783689156225067)
  ·
    refine ⟨17815298908175533734337601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11876865938783689156225067 17815298908175533734337601)
    ·
      refine ⟨13361474181131650300753201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17815298908175533734337601 13361474181131650300753201)
      ·
        refine ⟨10021105635848737725564901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13361474181131650300753201 10021105635848737725564901)
        ·
          refine ⟨1878957306721638323543419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10021105635848737725564901 1878957306721638323543419)
          ·
            refine ⟨2818435960082457485315129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878957306721638323543419 2818435960082457485315129)
            ·
              refine ⟨2113826970061843113986347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818435960082457485315129 2113826970061843113986347)
              ·
                refine ⟨3170740455092764670979521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113826970061843113986347 3170740455092764670979521)
                ·
                  refine ⟨2378055341319573503234641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3170740455092764670979521 2378055341319573503234641)
                  ·
                    refine ⟨1783541505989680127425981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2378055341319573503234641 1783541505989680127425981)
                    ·
                      refine ⟨668828064746130047784743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1783541505989680127425981 668828064746130047784743)
                      ·
                        rfl

theorem cell23_1302538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1302538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302538 prefixEnd_1302538 := by exact prefixLift 1302538
  have htrace : WordTrace (prefixWord ++ tailWord_1302538) baseStart_1302538 baseEnd_1302538 := by
    simpa [prefixWord, tailWord_1302538, baseEnd_1302538] using wordTrace_append hprefix tailTrace_1302538
  have hstable : (prefixWord ++ tailWord_1302538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302538).length < 2 ^ (prefixWord ++ tailWord_1302538).sum := by decide
  have hdescent : baseEnd_1302538 < baseStart_1302538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302676 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1302676 : Nat := 118140960795 + 1302676 * 2 ^ 59
def prefixEnd_1302676 : Nat := 4983230072969 + 3 ^ 40 * 1302676 * 2
def baseEnd_1302676 : Nat := 668898925076450507859109

theorem tailTrace_1302676 : CollatzResearch.WordTrace tailWord_1302676 prefixEnd_1302676 668898925076450507859109 := by
  unfold tailWord_1302676
  simp only [CollatzResearch.WordTrace]
  refine ⟨23756248514317403096711941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31674998019089870795615921 23756248514317403096711941)
  ·
    refine ⟨4454296596434513080633489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23756248514317403096711941 4454296596434513080633489)
    ·
      refine ⟨3340722447325884810475117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4454296596434513080633489 3340722447325884810475117)
      ·
        refine ⟨1252770917747206803928169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3340722447325884810475117 1252770917747206803928169)
        ·
          refine ⟨939578188310405102946127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252770917747206803928169 939578188310405102946127)
          ·
            refine ⟨1409367282465607654419191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939578188310405102946127 1409367282465607654419191)
            ·
              refine ⟨2114050923698411481628787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409367282465607654419191 2114050923698411481628787)
              ·
                refine ⟨3171076385547617222443181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114050923698411481628787 3171076385547617222443181)
                ·
                  refine ⟨1189153644580356458416193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3171076385547617222443181 1189153644580356458416193)
                  ·
                    refine ⟨891865233435267343812145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189153644580356458416193 891865233435267343812145)
                    ·
                      refine ⟨668898925076450507859109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891865233435267343812145 668898925076450507859109)
                      ·
                        rfl

theorem cell23_1302676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1302676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302676 prefixEnd_1302676 := by exact prefixLift 1302676
  have htrace : WordTrace (prefixWord ++ tailWord_1302676) baseStart_1302676 baseEnd_1302676 := by
    simpa [prefixWord, tailWord_1302676, baseEnd_1302676] using wordTrace_append hprefix tailTrace_1302676
  have hstable : (prefixWord ++ tailWord_1302676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302676).length < 2 ^ (prefixWord ++ tailWord_1302676).sum := by decide
  have hdescent : baseEnd_1302676 < baseStart_1302676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302731 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 3]
def baseStart_1302731 : Nat := 118140960795 + 1302731 * 2 ^ 59
def prefixEnd_1302731 : Nat := 4983230072969 + 3 ^ 40 * 1302731 * 2
def baseEnd_1302731 : Nat := 668927166512447792671355

theorem tailTrace_1302731 : CollatzResearch.WordTrace tailWord_1302731 prefixEnd_1302731 668927166512447792671355 := by
  unfold tailWord_1302731
  simp only [CollatzResearch.WordTrace]
  refine ⟨47514503043435550586676047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31676335362290367057784031 47514503043435550586676047)
  ·
    refine ⟨71271754565153325880014071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47514503043435550586676047 71271754565153325880014071)
    ·
      refine ⟨106907631847729988820021107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71271754565153325880014071 106907631847729988820021107)
      ·
        refine ⟨160361447771594983230031661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106907631847729988820021107 160361447771594983230031661)
        ·
          refine ⟨60135542914348118711261873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160361447771594983230031661 60135542914348118711261873)
          ·
            refine ⟨45101657185761089033446405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60135542914348118711261873 45101657185761089033446405)
            ·
              refine ⟨8456560722330204193771201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45101657185761089033446405 8456560722330204193771201)
              ·
                refine ⟨6342420541747653145328401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8456560722330204193771201 6342420541747653145328401)
                ·
                  refine ⟨4756815406310739858996301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6342420541747653145328401 4756815406310739858996301)
                  ·
                    refine ⟨1783805777366527447123613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4756815406310739858996301 1783805777366527447123613)
                    ·
                      refine ⟨668927166512447792671355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1783805777366527447123613 668927166512447792671355)
                      ·
                        rfl

theorem cell23_1302731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 3].length) (baseStart_1302731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302731 prefixEnd_1302731 := by exact prefixLift 1302731
  have htrace : WordTrace (prefixWord ++ tailWord_1302731) baseStart_1302731 baseEnd_1302731 := by
    simpa [prefixWord, tailWord_1302731, baseEnd_1302731] using wordTrace_append hprefix tailTrace_1302731
  have hstable : (prefixWord ++ tailWord_1302731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302731).length < 2 ^ (prefixWord ++ tailWord_1302731).sum := by decide
  have hdescent : baseEnd_1302731 < baseStart_1302731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302771 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4]
def baseStart_1302771 : Nat := 118140960795 + 1302771 * 2 ^ 59
def prefixEnd_1302771 : Nat := 4983230072969 + 3 ^ 40 * 1302771 * 2
def baseEnd_1302771 : Nat := 668947705738627636171171

theorem tailTrace_1302771 : CollatzResearch.WordTrace tailWord_1302771 prefixEnd_1302771 668947705738627636171171 := by
  unfold tailWord_1302771
  simp only [CollatzResearch.WordTrace]
  refine ⟨47515961963290637418132167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31677307975527091612088111 47515961963290637418132167)
  ·
    refine ⟨71273942944935956127198251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47515961963290637418132167 71273942944935956127198251)
    ·
      refine ⟨106910914417403934190797377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71273942944935956127198251 106910914417403934190797377)
      ·
        refine ⟨80183185813052950643098033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106910914417403934190797377 80183185813052950643098033)
        ·
          refine ⟨60137389359789712982323525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80183185813052950643098033 60137389359789712982323525)
          ·
            refine ⟨11275760504960571184185661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60137389359789712982323525 11275760504960571184185661)
            ·
              refine ⟨4228410189360214194069623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11275760504960571184185661 4228410189360214194069623)
              ·
                refine ⟨6342615284040321291104435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228410189360214194069623 6342615284040321291104435)
                ·
                  refine ⟨9513922926060481936656653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6342615284040321291104435 9513922926060481936656653)
                  ·
                    refine ⟨3567721097272680726246245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9513922926060481936656653 3567721097272680726246245)
                    ·
                      refine ⟨668947705738627636171171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3567721097272680726246245 668947705738627636171171)
                      ·
                        rfl

theorem cell23_1302771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_1302771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302771 prefixEnd_1302771 := by exact prefixLift 1302771
  have htrace : WordTrace (prefixWord ++ tailWord_1302771) baseStart_1302771 baseEnd_1302771 := by
    simpa [prefixWord, tailWord_1302771, baseEnd_1302771] using wordTrace_append hprefix tailTrace_1302771
  have hstable : (prefixWord ++ tailWord_1302771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302771).length < 2 ^ (prefixWord ++ tailWord_1302771).sum := by decide
  have hdescent : baseEnd_1302771 < baseStart_1302771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302811 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 6]
def baseStart_1302811 : Nat := 118140960795 + 1302811 * 2 ^ 59
def prefixEnd_1302811 : Nat := 4983230072969 + 3 ^ 40 * 1302811 * 2
def baseEnd_1302811 : Nat := 74329804996089719963443

theorem tailTrace_1302811 : CollatzResearch.WordTrace tailWord_1302811 prefixEnd_1302811 74329804996089719963443 := by
  unfold tailWord_1302811
  simp only [CollatzResearch.WordTrace]
  refine ⟨47517420883145724249588287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31678280588763816166392191 47517420883145724249588287)
  ·
    refine ⟨71276131324718586374382431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47517420883145724249588287 71276131324718586374382431)
    ·
      refine ⟨106914196987077879561573647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71276131324718586374382431 106914196987077879561573647)
      ·
        refine ⟨160371295480616819342360471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106914196987077879561573647 160371295480616819342360471)
        ·
          refine ⟨240556943220925229013540707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160371295480616819342360471 240556943220925229013540707)
          ·
            refine ⟨360835414831387843520311061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240556943220925229013540707 360835414831387843520311061)
            ·
              refine ⟨16914160070221305165014581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360835414831387843520311061 16914160070221305165014581)
              ·
                refine ⟨1585702506583247359220117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16914160070221305165014581 1585702506583247359220117)
                ·
                  refine ⟨74329804996089719963443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1585702506583247359220117 74329804996089719963443)
                  ·
                    rfl

theorem cell23_1302811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 6].length) (baseStart_1302811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302811 prefixEnd_1302811 := by exact prefixLift 1302811
  have htrace : WordTrace (prefixWord ++ tailWord_1302811) baseStart_1302811 baseEnd_1302811 := by
    simpa [prefixWord, tailWord_1302811, baseEnd_1302811] using wordTrace_append hprefix tailTrace_1302811
  have hstable : (prefixWord ++ tailWord_1302811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302811).length < 2 ^ (prefixWord ++ tailWord_1302811).sum := by decide
  have hdescent : baseEnd_1302811 < baseStart_1302811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302848 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 3, 5, 2]
def baseStart_1302848 : Nat := 118140960795 + 1302848 * 2 ^ 59
def prefixEnd_1302848 : Nat := 4983230072969 + 3 ^ 40 * 1302848 * 2
def baseEnd_1302848 : Nat := 668987243749023834908317

theorem tailTrace_1302848 : CollatzResearch.WordTrace tailWord_1302848 prefixEnd_1302848 668987243749023834908317 := by
  unfold tailWord_1302848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23759385192005839784342599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31679180256007786379123465 23759385192005839784342599)
  ·
    refine ⟨35639077788008759676513899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23759385192005839784342599 35639077788008759676513899)
    ·
      refine ⟨53458616682013139514770849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35639077788008759676513899 53458616682013139514770849)
      ·
        refine ⟨40093962511509854636078137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53458616682013139514770849 40093962511509854636078137)
        ·
          refine ⟨30070471883632390977058603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40093962511509854636078137 30070471883632390977058603)
          ·
            refine ⟨45105707825448586465587905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30070471883632390977058603 45105707825448586465587905)
            ·
              refine ⟨33829280869086439849190929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45105707825448586465587905 33829280869086439849190929)
              ·
                refine ⟨25371960651814829886893197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33829280869086439849190929 25371960651814829886893197)
                ·
                  refine ⟨9514485244430561207584949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25371960651814829886893197 9514485244430561207584949)
                  ·
                    refine ⟨891982991665365113211089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9514485244430561207584949 891982991665365113211089)
                    ·
                      refine ⟨668987243749023834908317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 891982991665365113211089 668987243749023834908317)
                      ·
                        rfl

theorem cell23_1302848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_1302848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302848 prefixEnd_1302848 := by exact prefixLift 1302848
  have htrace : WordTrace (prefixWord ++ tailWord_1302848) baseStart_1302848 baseEnd_1302848 := by
    simpa [prefixWord, tailWord_1302848, baseEnd_1302848] using wordTrace_append hprefix tailTrace_1302848
  have hstable : (prefixWord ++ tailWord_1302848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302848).length < 2 ^ (prefixWord ++ tailWord_1302848).sum := by decide
  have hdescent : baseEnd_1302848 < baseStart_1302848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302849 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1302849 : Nat := 118140960795 + 1302849 * 2 ^ 59
def prefixEnd_1302849 : Nat := 4983230072969 + 3 ^ 40 * 1302849 * 2
def baseEnd_1302849 : Nat := 222995919076559443665271

theorem tailTrace_1302849 : CollatzResearch.WordTrace tailWord_1302849 prefixEnd_1302849 222995919076559443665271 := by
  unfold tailWord_1302849
  simp only [CollatzResearch.WordTrace]
  refine ⟨47518806857008056739471601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31679204571338704492981067 47518806857008056739471601)
  ·
    refine ⟨35639105142756042554603701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47518806857008056739471601 35639105142756042554603701)
    ·
      refine ⟨3341166107133378989494097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35639105142756042554603701 3341166107133378989494097)
      ·
        refine ⟨2505874580350034242120573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3341166107133378989494097 2505874580350034242120573)
        ·
          refine ⟨939702967631262840795215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2505874580350034242120573 939702967631262840795215)
          ·
            refine ⟨1409554451446894261192823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939702967631262840795215 1409554451446894261192823)
            ·
              refine ⟨2114331677170341391789235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409554451446894261192823 2114331677170341391789235)
              ·
                refine ⟨3171497515755512087683853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114331677170341391789235 3171497515755512087683853)
                ·
                  refine ⟨1189311568408317032881445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3171497515755512087683853 1189311568408317032881445)
                  ·
                    refine ⟨222995919076559443665271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189311568408317032881445 222995919076559443665271)
                    ·
                      rfl

theorem cell23_1302849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1302849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302849 prefixEnd_1302849 := by exact prefixLift 1302849
  have htrace : WordTrace (prefixWord ++ tailWord_1302849) baseStart_1302849 baseEnd_1302849 := by
    simpa [prefixWord, tailWord_1302849, baseEnd_1302849] using wordTrace_append hprefix tailTrace_1302849
  have hstable : (prefixWord ++ tailWord_1302849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302849).length < 2 ^ (prefixWord ++ tailWord_1302849).sum := by decide
  have hdescent : baseEnd_1302849 < baseStart_1302849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302881 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_1302881 : Nat := 118140960795 + 1302881 * 2 ^ 59
def prefixEnd_1302881 : Nat := 4983230072969 + 3 ^ 40 * 1302881 * 2
def baseEnd_1302881 : Nat := 669004188610622205795665

theorem tailTrace_1302881 : CollatzResearch.WordTrace tailWord_1302881 prefixEnd_1302881 669004188610622205795665 := by
  unfold tailWord_1302881
  simp only [CollatzResearch.WordTrace]
  refine ⟨47519973992892126204636497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31679982661928084136424331 47519973992892126204636497)
  ·
    refine ⟨35639980494669094653477373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47519973992892126204636497 35639980494669094653477373)
    ·
      refine ⟨13364992685500910495054015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35639980494669094653477373 13364992685500910495054015)
      ·
        refine ⟨20047489028251365742581023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13364992685500910495054015 20047489028251365742581023)
        ·
          refine ⟨30071233542377048613871535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20047489028251365742581023 30071233542377048613871535)
          ·
            refine ⟨45106850313565572920807303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30071233542377048613871535 45106850313565572920807303)
            ·
              refine ⟨67660275470348359381210955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45106850313565572920807303 67660275470348359381210955)
              ·
                refine ⟨101490413205522539071816433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67660275470348359381210955 101490413205522539071816433)
                ·
                  refine ⟨76117809904141904303862325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101490413205522539071816433 76117809904141904303862325)
                  ·
                    refine ⟨7136044678513303528487093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76117809904141904303862325 7136044678513303528487093)
                    ·
                      refine ⟨669004188610622205795665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7136044678513303528487093 669004188610622205795665)
                      ·
                        rfl

theorem cell23_1302881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_1302881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302881 prefixEnd_1302881 := by exact prefixLift 1302881
  have htrace : WordTrace (prefixWord ++ tailWord_1302881) baseStart_1302881 baseEnd_1302881 := by
    simpa [prefixWord, tailWord_1302881, baseEnd_1302881] using wordTrace_append hprefix tailTrace_1302881
  have hstable : (prefixWord ++ tailWord_1302881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302881).length < 2 ^ (prefixWord ++ tailWord_1302881).sum := by decide
  have hdescent : baseEnd_1302881 < baseStart_1302881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302882 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1302882 : Nat := 118140960795 + 1302882 * 2 ^ 59
def prefixEnd_1302882 : Nat := 4983230072969 + 3 ^ 40 * 1302882 * 2
def baseEnd_1302882 : Nat := 669004702091276701883161

theorem tailTrace_1302882 : CollatzResearch.WordTrace tailWord_1302882 prefixEnd_1302882 669004702091276701883161 := by
  unfold tailWord_1302882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880002616472125843855725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31680006977259002250281933 11880002616472125843855725)
  ·
    refine ⟨4455000981177047191445897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11880002616472125843855725 4455000981177047191445897)
    ·
      refine ⟨3341250735882785393584423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4455000981177047191445897 3341250735882785393584423)
      ·
        refine ⟨5011876103824178090376635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341250735882785393584423 5011876103824178090376635)
        ·
          refine ⟨7517814155736267135564953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011876103824178090376635 7517814155736267135564953)
          ·
            refine ⟨5638360616802200351673715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7517814155736267135564953 5638360616802200351673715)
            ·
              refine ⟨8457540925203300527510573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638360616802200351673715 8457540925203300527510573)
              ·
                refine ⟨3171577846951237697816465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8457540925203300527510573 3171577846951237697816465)
                ·
                  refine ⟨2378683385213428273362349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3171577846951237697816465 2378683385213428273362349)
                  ·
                    refine ⟨892006269455035602510881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2378683385213428273362349 892006269455035602510881)
                    ·
                      refine ⟨669004702091276701883161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892006269455035602510881 669004702091276701883161)
                      ·
                        rfl

theorem cell23_1302882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1302882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302882 prefixEnd_1302882 := by exact prefixLift 1302882
  have htrace : WordTrace (prefixWord ++ tailWord_1302882) baseStart_1302882 baseEnd_1302882 := by
    simpa [prefixWord, tailWord_1302882, baseEnd_1302882] using wordTrace_append hprefix tailTrace_1302882
  have hstable : (prefixWord ++ tailWord_1302882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302882).length < 2 ^ (prefixWord ++ tailWord_1302882).sum := by decide
  have hdescent : baseEnd_1302882 < baseStart_1302882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302888 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1302888 : Nat := 118140960795 + 1302888 * 2 ^ 59
def prefixEnd_1302888 : Nat := 4983230072969 + 3 ^ 40 * 1302888 * 2
def baseEnd_1302888 : Nat := 223002594325067892802711

theorem tailTrace_1302888 : CollatzResearch.WordTrace tailWord_1302888 prefixEnd_1302888 223002594325067892802711 := by
  unfold tailWord_1302888
  simp only [CollatzResearch.WordTrace]
  refine ⟨23760114651933383200070659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31680152869244510933427545 23760114651933383200070659)
  ·
    refine ⟨35640171977900074800105989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23760114651933383200070659 35640171977900074800105989)
    ·
      refine ⟨6682532245856264025019873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35640171977900074800105989 6682532245856264025019873)
      ·
        refine ⟨5011899184392198018764905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6682532245856264025019873 5011899184392198018764905)
        ·
          refine ⟨3758924388294148514073679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5011899184392198018764905 3758924388294148514073679)
          ·
            refine ⟨5638386582441222771110519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3758924388294148514073679 5638386582441222771110519)
            ·
              refine ⟨8457579873661834156665779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638386582441222771110519 8457579873661834156665779)
              ·
                refine ⟨12686369810492751234998669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457579873661834156665779 12686369810492751234998669)
                ·
                  refine ⟨4757388678934781713124501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12686369810492751234998669 4757388678934781713124501)
                  ·
                    refine ⟨223002594325067892802711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4757388678934781713124501 223002594325067892802711)
                    ·
                      rfl

theorem cell23_1302888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1302888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302888 prefixEnd_1302888 := by exact prefixLift 1302888
  have htrace : WordTrace (prefixWord ++ tailWord_1302888) baseStart_1302888 baseEnd_1302888 := by
    simpa [prefixWord, tailWord_1302888, baseEnd_1302888] using wordTrace_append hprefix tailTrace_1302888
  have hstable : (prefixWord ++ tailWord_1302888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302888).length < 2 ^ (prefixWord ++ tailWord_1302888).sum := by decide
  have hdescent : baseEnd_1302888 < baseStart_1302888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302892 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_1302892 : Nat := 118140960795 + 1302892 * 2 ^ 59
def prefixEnd_1302892 : Nat := 4983230072969 + 3 ^ 40 * 1302892 * 2
def baseEnd_1302892 : Nat := 223003278965940554252705

theorem tailTrace_1302892 : CollatzResearch.WordTrace tailWord_1302892 prefixEnd_1302892 223003278965940554252705 := by
  unfold tailWord_1302892
  simp only [CollatzResearch.WordTrace]
  refine ⟨23760187597926137541643465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31680250130568183388857953 23760187597926137541643465)
  ·
    refine ⟨17820140698444603156232599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23760187597926137541643465 17820140698444603156232599)
    ·
      refine ⟨26730211047666904734348899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17820140698444603156232599 26730211047666904734348899)
      ·
        refine ⟨40095316571500357101523349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26730211047666904734348899 40095316571500357101523349)
        ·
          refine ⟨1879467964289079239133907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40095316571500357101523349 1879467964289079239133907)
          ·
            refine ⟨2819201946433618858700861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879467964289079239133907 2819201946433618858700861)
            ·
              refine ⟨1057200729912607072012823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2819201946433618858700861 1057200729912607072012823)
              ·
                refine ⟨1585801094868910608019235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057200729912607072012823 1585801094868910608019235)
                ·
                  refine ⟨2378701642303365912028853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585801094868910608019235 2378701642303365912028853)
                  ·
                    refine ⟨223003278965940554252705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2378701642303365912028853 223003278965940554252705)
                    ·
                      rfl

theorem cell23_1302892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_1302892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302892 prefixEnd_1302892 := by exact prefixLift 1302892
  have htrace : WordTrace (prefixWord ++ tailWord_1302892) baseStart_1302892 baseEnd_1302892 := by
    simpa [prefixWord, tailWord_1302892, baseEnd_1302892] using wordTrace_append hprefix tailTrace_1302892
  have hstable : (prefixWord ++ tailWord_1302892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302892).length < 2 ^ (prefixWord ++ tailWord_1302892).sum := by decide
  have hdescent : baseEnd_1302892 < baseStart_1302892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302895 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 7, 2, 2]
def baseStart_1302895 : Nat := 118140960795 + 1302895 * 2 ^ 59
def prefixEnd_1302895 : Nat := 4983230072969 + 3 ^ 40 * 1302895 * 2
def baseEnd_1302895 : Nat := 669011377339785151020601

theorem tailTrace_1302895 : CollatzResearch.WordTrace tailWord_1302895 prefixEnd_1302895 669011377339785151020601 := by
  unfold tailWord_1302895
  simp only [CollatzResearch.WordTrace]
  refine ⟨47520484614841406595646139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31680323076560937730430759 47520484614841406595646139)
  ·
    refine ⟨71280726922262109893469209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47520484614841406595646139 71280726922262109893469209)
    ·
      refine ⟨53460545191696582420101907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71280726922262109893469209 53460545191696582420101907)
      ·
        refine ⟨80190817787544873630152861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53460545191696582420101907 80190817787544873630152861)
        ·
          refine ⟨30071556670329327611307323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80190817787544873630152861 30071556670329327611307323)
          ·
            refine ⟨45107335005493991416960985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30071556670329327611307323 45107335005493991416960985)
            ·
              refine ⟨33830501254120493562720739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45107335005493991416960985 33830501254120493562720739)
              ·
                refine ⟨50745751881180740344081109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33830501254120493562720739 50745751881180740344081109)
                ·
                  refine ⟨1189353559715173601814401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 50745751881180740344081109 1189353559715173601814401)
                  ·
                    refine ⟨892015169786380201360801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189353559715173601814401 892015169786380201360801)
                    ·
                      refine ⟨669011377339785151020601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892015169786380201360801 669011377339785151020601)
                      ·
                        rfl

theorem cell23_1302895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 2, 2].length) (baseStart_1302895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302895 prefixEnd_1302895 := by exact prefixLift 1302895
  have htrace : WordTrace (prefixWord ++ tailWord_1302895) baseStart_1302895 baseEnd_1302895 := by
    simpa [prefixWord, tailWord_1302895, baseEnd_1302895] using wordTrace_append hprefix tailTrace_1302895
  have hstable : (prefixWord ++ tailWord_1302895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302895).length < 2 ^ (prefixWord ++ tailWord_1302895).sum := by decide
  have hdescent : baseEnd_1302895 < baseStart_1302895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302922 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_1302922 : Nat := 118140960795 + 1302922 * 2 ^ 59
def prefixEnd_1302922 : Nat := 4983230072969 + 3 ^ 40 * 1302922 * 2
def baseEnd_1302922 : Nat := 223008413772485515127659

theorem tailTrace_1302922 : CollatzResearch.WordTrace tailWord_1302922 prefixEnd_1302922 223008413772485515127659 := by
  unfold tailWord_1302922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880367346435897551719755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31680979590495726804586013 11880367346435897551719755)
  ·
    refine ⟨17820551019653846327579633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11880367346435897551719755 17820551019653846327579633)
    ·
      refine ⟨13365413264740384745684725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17820551019653846327579633 13365413264740384745684725)
      ·
        refine ⟨1253007493569411069907943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13365413264740384745684725 1253007493569411069907943)
        ·
          refine ⟨1879511240354116604861915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253007493569411069907943 1879511240354116604861915)
          ·
            refine ⟨2819266860531174907292873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879511240354116604861915 2819266860531174907292873)
            ·
              refine ⟨2114450145398381180469655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819266860531174907292873 2114450145398381180469655)
              ·
                refine ⟨3171675218097571770704483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114450145398381180469655 3171675218097571770704483)
                ·
                  refine ⟨4757512827146357656056725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171675218097571770704483 4757512827146357656056725)
                  ·
                    refine ⟨223008413772485515127659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4757512827146357656056725 223008413772485515127659)
                    ·
                      rfl

theorem cell23_1302922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_1302922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302922 prefixEnd_1302922 := by exact prefixLift 1302922
  have htrace : WordTrace (prefixWord ++ tailWord_1302922) baseStart_1302922 baseEnd_1302922 := by
    simpa [prefixWord, tailWord_1302922, baseEnd_1302922] using wordTrace_append hprefix tailTrace_1302922
  have hstable : (prefixWord ++ tailWord_1302922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302922).length < 2 ^ (prefixWord ++ tailWord_1302922).sum := by decide
  have hdescent : baseEnd_1302922 < baseStart_1302922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302942 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1302942 : Nat := 118140960795 + 1302942 * 2 ^ 59
def prefixEnd_1302942 : Nat := 4983230072969 + 3 ^ 40 * 1302942 * 2
def baseEnd_1302942 : Nat := 669035510930546467132885

theorem tailTrace_1302942 : CollatzResearch.WordTrace tailWord_1302942 prefixEnd_1302942 669035510930546467132885 := by
  unfold tailWord_1302942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940274855708891702825885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31681465897114089081738053 5940274855708891702825885)
  ·
    refine ⟨2227603070890834388559707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5940274855708891702825885 2227603070890834388559707)
    ·
      refine ⟨3341404606336251582839561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227603070890834388559707 3341404606336251582839561)
      ·
        refine ⟨2506053454752188687129671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3341404606336251582839561 2506053454752188687129671)
        ·
          refine ⟨3759080182128283030694507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2506053454752188687129671 3759080182128283030694507)
          ·
            refine ⟨5638620273192424546041761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759080182128283030694507 5638620273192424546041761)
            ·
              refine ⟨4228965204894318409531321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5638620273192424546041761 4228965204894318409531321)
              ·
                refine ⟨3171723903670738807148491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4228965204894318409531321 3171723903670738807148491)
                ·
                  refine ⟨4757585855506108210722737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171723903670738807148491 4757585855506108210722737)
                  ·
                    refine ⟨3568189391629581158042053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4757585855506108210722737 3568189391629581158042053)
                    ·
                      refine ⟨669035510930546467132885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3568189391629581158042053 669035510930546467132885)
                      ·
                        rfl

theorem cell23_1302942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1302942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302942 prefixEnd_1302942 := by exact prefixLift 1302942
  have htrace : WordTrace (prefixWord ++ tailWord_1302942) baseStart_1302942 baseEnd_1302942 := by
    simpa [prefixWord, tailWord_1302942, baseEnd_1302942] using wordTrace_append hprefix tailTrace_1302942
  have hstable : (prefixWord ++ tailWord_1302942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302942).length < 2 ^ (prefixWord ++ tailWord_1302942).sum := by decide
  have hdescent : baseEnd_1302942 < baseStart_1302942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302946 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_1302946 : Nat := 118140960795 + 1302946 * 2 ^ 59
def prefixEnd_1302946 : Nat := 4983230072969 + 3 ^ 40 * 1302946 * 2
def baseEnd_1302946 : Nat := 669037564853164451482867

theorem tailTrace_1302946 : CollatzResearch.WordTrace tailWord_1302946 prefixEnd_1302946 669037564853164451482867 := by
  unfold tailWord_1302946
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880586184414160576438173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31681563158437761537168461 11880586184414160576438173)
  ·
    refine ⟨4455219819155310216164315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11880586184414160576438173 4455219819155310216164315)
    ·
      refine ⟨6682829728732965324246473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455219819155310216164315 6682829728732965324246473)
      ·
        refine ⟨5012122296549723993184855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6682829728732965324246473 5012122296549723993184855)
        ·
          refine ⟨7518183444824585989777283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012122296549723993184855 7518183444824585989777283)
          ·
            refine ⟨11277275167236878984665925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518183444824585989777283 11277275167236878984665925)
            ·
              refine ⟨2114489093856914809624861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11277275167236878984665925 2114489093856914809624861)
              ·
                refine ⟨792933410196343053609323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2114489093856914809624861 792933410196343053609323)
                ·
                  refine ⟨1189400115294514580413985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792933410196343053609323 1189400115294514580413985)
                  ·
                    refine ⟨892050086470885935310489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189400115294514580413985 892050086470885935310489)
                    ·
                      refine ⟨669037564853164451482867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892050086470885935310489 669037564853164451482867)
                      ·
                        rfl

theorem cell23_1302946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_1302946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1302946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1302946 prefixEnd_1302946 := by exact prefixLift 1302946
  have htrace : WordTrace (prefixWord ++ tailWord_1302946) baseStart_1302946 baseEnd_1302946 := by
    simpa [prefixWord, tailWord_1302946, baseEnd_1302946] using wordTrace_append hprefix tailTrace_1302946
  have hstable : (prefixWord ++ tailWord_1302946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302946).length < 2 ^ (prefixWord ++ tailWord_1302946).sum := by decide
  have hdescent : baseEnd_1302946 < baseStart_1302946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303002 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2]
def baseStart_1303002 : Nat := 118140960795 + 1303002 * 2 ^ 59
def prefixEnd_1303002 : Nat := 4983230072969 + 3 ^ 40 * 1303002 * 2
def baseEnd_1303002 : Nat := 669066319769816232382609

theorem tailTrace_1303002 : CollatzResearch.WordTrace tailWord_1303002 prefixEnd_1303002 669066319769816232382609 := by
  unfold tailWord_1303002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881096806363440967447815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31682924816969175913194173 11881096806363440967447815)
  ·
    refine ⟨17821645209545161451171723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11881096806363440967447815 17821645209545161451171723)
    ·
      refine ⟨26732467814317742176757585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17821645209545161451171723 26732467814317742176757585)
      ·
        refine ⟨20049350860738306632568189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26732467814317742176757585 20049350860738306632568189)
        ·
          refine ⟨7518506572776864987213071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20049350860738306632568189 7518506572776864987213071)
          ·
            refine ⟨11277759859165297480819607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518506572776864987213071 11277759859165297480819607)
            ·
              refine ⟨16916639788747946221229411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11277759859165297480819607 16916639788747946221229411)
              ·
                refine ⟨25374959683121919331844117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16916639788747946221229411 25374959683121919331844117)
                ·
                  refine ⟨1189451235146339968680193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25374959683121919331844117 1189451235146339968680193)
                  ·
                    refine ⟨892088426359754976510145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189451235146339968680193 892088426359754976510145)
                    ·
                      refine ⟨669066319769816232382609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892088426359754976510145 669066319769816232382609)
                      ·
                        rfl

theorem cell23_1303002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_1303002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303002 prefixEnd_1303002 := by exact prefixLift 1303002
  have htrace : WordTrace (prefixWord ++ tailWord_1303002) baseStart_1303002 baseEnd_1303002 := by
    simpa [prefixWord, tailWord_1303002, baseEnd_1303002] using wordTrace_append hprefix tailTrace_1303002
  have hstable : (prefixWord ++ tailWord_1303002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303002).length < 2 ^ (prefixWord ++ tailWord_1303002).sum := by decide
  have hdescent : baseEnd_1303002 < baseStart_1303002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303005 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1303005 : Nat := 118140960795 + 1303005 * 2 ^ 59
def prefixEnd_1303005 : Nat := 4983230072969 + 3 ^ 40 * 1303005 * 2
def baseEnd_1303005 : Nat := 669067860211779720645095

theorem tailTrace_1303005 : CollatzResearch.WordTrace tailWord_1303005 prefixEnd_1303005 669067860211779720645095 := by
  unfold tailWord_1303005
  simp only [CollatzResearch.WordTrace]
  refine ⟨47524496644442895382150469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31682997762961930254766979 47524496644442895382150469)
  ·
    refine ⟨8910843120833042884153213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47524496644442895382150469 8910843120833042884153213)
    ·
      refine ⟨3341566170312391081557455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8910843120833042884153213 3341566170312391081557455)
      ·
        refine ⟨5012349255468586622336183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341566170312391081557455 5012349255468586622336183)
        ·
          refine ⟨7518523883202879933504275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012349255468586622336183 7518523883202879933504275)
          ·
            refine ⟨11277785824804319900256413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7518523883202879933504275 11277785824804319900256413)
            ·
              refine ⟨4229169684301619962596155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11277785824804319900256413 4229169684301619962596155)
              ·
                refine ⟨6343754526452429943894233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229169684301619962596155 6343754526452429943894233)
                ·
                  refine ⟨4757815894839322457920675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6343754526452429943894233 4757815894839322457920675)
                  ·
                    refine ⟨7136723842258983686881013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4757815894839322457920675 7136723842258983686881013)
                    ·
                      refine ⟨669067860211779720645095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7136723842258983686881013 669067860211779720645095)
                      ·
                        rfl

theorem cell23_1303005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1303005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303005 prefixEnd_1303005 := by exact prefixLift 1303005
  have htrace : WordTrace (prefixWord ++ tailWord_1303005) baseStart_1303005 baseEnd_1303005 := by
    simpa [prefixWord, tailWord_1303005, baseEnd_1303005] using wordTrace_append hprefix tailTrace_1303005
  have hstable : (prefixWord ++ tailWord_1303005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303005).length < 2 ^ (prefixWord ++ tailWord_1303005).sum := by decide
  have hdescent : baseEnd_1303005 < baseStart_1303005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303048 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1303048 : Nat := 118140960795 + 1303048 * 2 ^ 59
def prefixEnd_1303048 : Nat := 4983230072969 + 3 ^ 40 * 1303048 * 2
def baseEnd_1303048 : Nat := 669089939879923052407397

theorem tailTrace_1303048 : CollatzResearch.WordTrace tailWord_1303048 prefixEnd_1303048 669089939879923052407397 := by
  unfold tailWord_1303048
  simp only [CollatzResearch.WordTrace]
  refine ⟨23763032491643556862982899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31684043322191409150643865 23763032491643556862982899)
  ·
    refine ⟨35644548737465335294474349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23763032491643556862982899 35644548737465335294474349)
    ·
      refine ⟨13366705776549500735427881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35644548737465335294474349 13366705776549500735427881)
      ·
        refine ⟨10025029332412125551570911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13366705776549500735427881 10025029332412125551570911)
        ·
          refine ⟨15037543998618188327356367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10025029332412125551570911 15037543998618188327356367)
          ·
            refine ⟨22556315997927282491034551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15037543998618188327356367 22556315997927282491034551)
            ·
              refine ⟨33834473996890923736551827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22556315997927282491034551 33834473996890923736551827)
              ·
                refine ⟨50751710995336385604827741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33834473996890923736551827 50751710995336385604827741)
                ·
                  refine ⟨19031891623251144601810403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50751710995336385604827741 19031891623251144601810403)
                  ·
                    refine ⟨28547837434876716902715605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19031891623251144601810403 28547837434876716902715605)
                    ·
                      refine ⟨669089939879923052407397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28547837434876716902715605 669089939879923052407397)
                      ·
                        rfl

theorem cell23_1303048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1303048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303048 prefixEnd_1303048 := by exact prefixLift 1303048
  have htrace : WordTrace (prefixWord ++ tailWord_1303048) baseStart_1303048 baseEnd_1303048 := by
    simpa [prefixWord, tailWord_1303048, baseEnd_1303048] using wordTrace_append hprefix tailTrace_1303048
  have hstable : (prefixWord ++ tailWord_1303048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303048).length < 2 ^ (prefixWord ++ tailWord_1303048).sum := by decide
  have hdescent : baseEnd_1303048 < baseStart_1303048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303095 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_1303095 : Nat := 118140960795 + 1303095 * 2 ^ 59
def prefixEnd_1303095 : Nat := 4983230072969 + 3 ^ 40 * 1303095 * 2
def baseEnd_1303095 : Nat := 669114073470684368519681

theorem tailTrace_1303095 : CollatzResearch.WordTrace tailWord_1303095 prefixEnd_1303095 669114073470684368519681 := by
  unfold tailWord_1303095
  simp only [CollatzResearch.WordTrace]
  refine ⟨47527779214116840752926739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31685186142744560501951159 47527779214116840752926739)
  ·
    refine ⟨71291668821175261129390109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47527779214116840752926739 71291668821175261129390109)
    ·
      refine ⟨26734375807940722923521291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71291668821175261129390109 26734375807940722923521291)
      ·
        refine ⟨40101563711911084385281937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26734375807940722923521291 40101563711911084385281937)
        ·
          refine ⟨30076172783933313288961453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40101563711911084385281937 30076172783933313288961453)
          ·
            refine ⟨11278564793974992483360545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30076172783933313288961453 11278564793974992483360545)
            ·
              refine ⟨8458923595481244362520409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11278564793974992483360545 8458923595481244362520409)
              ·
                refine ⟨6344192696610933271890307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8458923595481244362520409 6344192696610933271890307)
                ·
                  refine ⟨9516289044916399907835461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6344192696610933271890307 9516289044916399907835461)
                  ·
                    refine ⟨1784304195921824982719149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9516289044916399907835461 1784304195921824982719149)
                    ·
                      refine ⟨669114073470684368519681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1784304195921824982719149 669114073470684368519681)
                      ·
                        rfl

theorem cell23_1303095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_1303095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303095 prefixEnd_1303095 := by exact prefixLift 1303095
  have htrace : WordTrace (prefixWord ++ tailWord_1303095) baseStart_1303095 baseEnd_1303095 := by
    simpa [prefixWord, tailWord_1303095, baseEnd_1303095] using wordTrace_append hprefix tailTrace_1303095
  have hstable : (prefixWord ++ tailWord_1303095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303095).length < 2 ^ (prefixWord ++ tailWord_1303095).sum := by decide
  have hdescent : baseEnd_1303095 < baseStart_1303095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303132 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 8]
def baseStart_1303132 : Nat := 118140960795 + 1303132 * 2 ^ 59
def prefixEnd_1303132 : Nat := 4983230072969 + 3 ^ 40 * 1303132 * 2
def baseEnd_1303132 : Nat := 74348119139433413750779

theorem tailTrace_1303132 : CollatzResearch.WordTrace tailWord_1303132 prefixEnd_1303132 74348119139433413750779 := by
  unfold tailWord_1303132
  simp only [CollatzResearch.WordTrace]
  refine ⟨23764564357491398036011825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31686085809988530714682433 23764564357491398036011825)
  ·
    refine ⟨17823423268118548527008869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23764564357491398036011825 17823423268118548527008869)
    ·
      refine ⟨3341891862772227848814163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17823423268118548527008869 3341891862772227848814163)
      ·
        refine ⟨5012837794158341773221245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341891862772227848814163 5012837794158341773221245)
        ·
          refine ⟨1879814172809378164957967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5012837794158341773221245 1879814172809378164957967)
          ·
            refine ⟨2819721259214067247436951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879814172809378164957967 2819721259214067247436951)
            ·
              refine ⟨4229581888821100871155427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819721259214067247436951 4229581888821100871155427)
              ·
                refine ⟨6344372833231651306733141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4229581888821100871155427 6344372833231651306733141)
                ·
                  refine ⟨74348119139433413750779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6344372833231651306733141 74348119139433413750779)
                  ·
                    rfl

theorem cell23_1303132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_1303132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303132 prefixEnd_1303132 := by exact prefixLift 1303132
  have htrace : WordTrace (prefixWord ++ tailWord_1303132) baseStart_1303132 baseEnd_1303132 := by
    simpa [prefixWord, tailWord_1303132, baseEnd_1303132] using wordTrace_append hprefix tailTrace_1303132
  have hstable : (prefixWord ++ tailWord_1303132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303132).length < 2 ^ (prefixWord ++ tailWord_1303132).sum := by decide
  have hdescent : baseEnd_1303132 < baseStart_1303132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303149 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1303149 : Nat := 118140960795 + 1303149 * 2 ^ 59
def prefixEnd_1303149 : Nat := 4983230072969 + 3 ^ 40 * 1303149 * 2
def baseEnd_1303149 : Nat := 74349089047336350804937

theorem tailTrace_1303149 : CollatzResearch.WordTrace tailWord_1303149 prefixEnd_1303149 74349089047336350804937 := by
  unfold tailWord_1303149
  simp only [CollatzResearch.WordTrace]
  refine ⟨47529748755921207975392501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31686499170614138650261667 47529748755921207975392501)
  ·
    refine ⟨4455913945867613247693047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47529748755921207975392501 4455913945867613247693047)
    ·
      refine ⟨6683870918801419871539571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455913945867613247693047 6683870918801419871539571)
      ·
        refine ⟨10025806378202129807309357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6683870918801419871539571 10025806378202129807309357)
        ·
          refine ⟨3759677391825798677741009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10025806378202129807309357 3759677391825798677741009)
          ·
            refine ⟨2819758043869349008305757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759677391825798677741009 2819758043869349008305757)
            ·
              refine ⟨1057409266451005878114659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2819758043869349008305757 1057409266451005878114659)
              ·
                refine ⟨1586113899676508817171989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057409266451005878114659 1586113899676508817171989)
                ·
                  refine ⟨74349089047336350804937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1586113899676508817171989 74349089047336350804937)
                  ·
                    rfl

theorem cell23_1303149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1303149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303149 prefixEnd_1303149 := by exact prefixLift 1303149
  have htrace : WordTrace (prefixWord ++ tailWord_1303149) baseStart_1303149 baseEnd_1303149 := by
    simpa [prefixWord, tailWord_1303149, baseEnd_1303149] using wordTrace_append hprefix tailTrace_1303149
  have hstable : (prefixWord ++ tailWord_1303149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303149).length < 2 ^ (prefixWord ++ tailWord_1303149).sum := by decide
  have hdescent : baseEnd_1303149 < baseStart_1303149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303169 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_1303169 : Nat := 118140960795 + 1303169 * 2 ^ 59
def prefixEnd_1303169 : Nat := 4983230072969 + 3 ^ 40 * 1303169 * 2
def baseEnd_1303169 : Nat := 669152071039117078994341

theorem tailTrace_1303169 : CollatzResearch.WordTrace tailWord_1303169 prefixEnd_1303169 669152071039117078994341 := by
  unfold tailWord_1303169
  simp only [CollatzResearch.WordTrace]
  refine ⟨47530478215848751391120561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31686985477232500927413707 47530478215848751391120561)
  ·
    refine ⟨35647858661886563543340421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47530478215848751391120561 35647858661886563543340421)
    ·
      refine ⟨6683973499103730664376329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35647858661886563543340421 6683973499103730664376329)
      ·
        refine ⟨5012980124327797998282247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6683973499103730664376329 5012980124327797998282247)
        ·
          refine ⟨7519470186491696997423371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012980124327797998282247 7519470186491696997423371)
          ·
            refine ⟨11279205279737545496135057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519470186491696997423371 11279205279737545496135057)
            ·
              refine ⟨8459403959803159122101293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11279205279737545496135057 8459403959803159122101293)
              ·
                refine ⟨3172276484926184670787985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8459403959803159122101293 3172276484926184670787985)
                ·
                  refine ⟨2379207363694638503090989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172276484926184670787985 2379207363694638503090989)
                  ·
                    refine ⟨892202761385489438659121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379207363694638503090989 892202761385489438659121)
                    ·
                      refine ⟨669152071039117078994341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892202761385489438659121 669152071039117078994341)
                      ·
                        rfl

theorem cell23_1303169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_1303169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303169 prefixEnd_1303169 := by exact prefixLift 1303169
  have htrace : WordTrace (prefixWord ++ tailWord_1303169) baseStart_1303169 baseEnd_1303169 := by
    simpa [prefixWord, tailWord_1303169, baseEnd_1303169] using wordTrace_append hprefix tailTrace_1303169
  have hstable : (prefixWord ++ tailWord_1303169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303169).length < 2 ^ (prefixWord ++ tailWord_1303169).sum := by decide
  have hdescent : baseEnd_1303169 < baseStart_1303169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303175 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 3, 6]
def baseStart_1303175 : Nat := 118140960795 + 1303175 * 2 ^ 59
def prefixEnd_1303175 : Nat := 4983230072969 + 3 ^ 40 * 1303175 * 2
def baseEnd_1303175 : Nat := 223051717307681351839771

theorem tailTrace_1303175 : CollatzResearch.WordTrace tailWord_1303175 prefixEnd_1303175 223051717307681351839771 := by
  unfold tailWord_1303175
  simp only [CollatzResearch.WordTrace]
  refine ⟨47530697053827014415838979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31687131369218009610559319 47530697053827014415838979)
  ·
    refine ⟨71296045580740521623758469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47530697053827014415838979 71296045580740521623758469)
    ·
      refine ⟨13368008546388847804454713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71296045580740521623758469 13368008546388847804454713)
      ·
        refine ⟨10026006409791635853341035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13368008546388847804454713 10026006409791635853341035)
        ·
          refine ⟨15039009614687453780011553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10026006409791635853341035 15039009614687453780011553)
          ·
            refine ⟨11279257211015590335008665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15039009614687453780011553 11279257211015590335008665)
            ·
              refine ⟨8459442908261692751256499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11279257211015590335008665 8459442908261692751256499)
              ·
                refine ⟨12689164362392539126884749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459442908261692751256499 12689164362392539126884749)
                ·
                  refine ⟨4758436635897202172581781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12689164362392539126884749 4758436635897202172581781)
                  ·
                    refine ⟨223051717307681351839771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4758436635897202172581781 223051717307681351839771)
                    ·
                      rfl

theorem cell23_1303175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_1303175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303175 prefixEnd_1303175 := by exact prefixLift 1303175
  have htrace : WordTrace (prefixWord ++ tailWord_1303175) baseStart_1303175 baseEnd_1303175 := by
    simpa [prefixWord, tailWord_1303175, baseEnd_1303175] using wordTrace_append hprefix tailTrace_1303175
  have hstable : (prefixWord ++ tailWord_1303175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303175).length < 2 ^ (prefixWord ++ tailWord_1303175).sum := by decide
  have hdescent : baseEnd_1303175 < baseStart_1303175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303185 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_1303185 : Nat := 118140960795 + 1303185 * 2 ^ 59
def prefixEnd_1303185 : Nat := 4983230072969 + 3 ^ 40 * 1303185 * 2
def baseEnd_1303185 : Nat := 669160286729589016394267

theorem tailTrace_1303185 : CollatzResearch.WordTrace tailWord_1303185 prefixEnd_1303185 669160286729589016394267 := by
  unfold tailWord_1303185
  simp only [CollatzResearch.WordTrace]
  refine ⟨47531061783790786123703009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31687374522527190749135339 47531061783790786123703009)
  ·
    refine ⟨35648296337843089592777257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47531061783790786123703009 35648296337843089592777257)
    ·
      refine ⟨26736222253382317194582943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35648296337843089592777257 26736222253382317194582943)
      ·
        refine ⟨40104333380073475791874415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26736222253382317194582943 40104333380073475791874415)
        ·
          refine ⟨60156500070110213687811623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40104333380073475791874415 60156500070110213687811623)
          ·
            refine ⟨90234750105165320531717435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60156500070110213687811623 90234750105165320531717435)
            ·
              refine ⟨135352125157747980797576153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90234750105165320531717435 135352125157747980797576153)
              ·
                refine ⟨101514093868310985598182115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135352125157747980797576153 101514093868310985598182115)
                ·
                  refine ⟨152271140802466478397273173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101514093868310985598182115 152271140802466478397273173)
                  ·
                    refine ⟨1784427431278904043718045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 152271140802466478397273173 1784427431278904043718045)
                    ·
                      refine ⟨669160286729589016394267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1784427431278904043718045 669160286729589016394267)
                      ·
                        rfl

theorem cell23_1303185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_1303185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303185 prefixEnd_1303185 := by exact prefixLift 1303185
  have htrace : WordTrace (prefixWord ++ tailWord_1303185) baseStart_1303185 baseEnd_1303185 := by
    simpa [prefixWord, tailWord_1303185, baseEnd_1303185] using wordTrace_append hprefix tailTrace_1303185
  have hstable : (prefixWord ++ tailWord_1303185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303185).length < 2 ^ (prefixWord ++ tailWord_1303185).sum := by decide
  have hdescent : baseEnd_1303185 < baseStart_1303185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303186 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_1303186 : Nat := 118140960795 + 1303186 * 2 ^ 59
def prefixEnd_1303186 : Nat := 4983230072969 + 3 ^ 40 * 1303186 * 2
def baseEnd_1303186 : Nat := 669160800210243512481763

theorem tailTrace_1303186 : CollatzResearch.WordTrace tailWord_1303186 prefixEnd_1303186 669160800210243512481763 := by
  unfold tailWord_1303186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11882774564196790823622353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31687398837858108862992941 11882774564196790823622353)
  ·
    refine ⟨8912080923147593117716765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11882774564196790823622353 8912080923147593117716765)
    ·
      refine ⟨3342030346180347419143787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8912080923147593117716765 3342030346180347419143787)
      ·
        refine ⟨5013045519270521128715681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342030346180347419143787 5013045519270521128715681)
        ·
          refine ⟨3759784139452890846536761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5013045519270521128715681 3759784139452890846536761)
          ·
            refine ⟨2819838104589668134902571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759784139452890846536761 2819838104589668134902571)
            ·
              refine ⟨4229757156884502202353857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819838104589668134902571 4229757156884502202353857)
              ·
                refine ⟨3172317867663376651765393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4229757156884502202353857 3172317867663376651765393)
                ·
                  refine ⟨2379238400747532488824045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172317867663376651765393 2379238400747532488824045)
                  ·
                    refine ⟨892214400280324683309017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379238400747532488824045 892214400280324683309017)
                    ·
                      refine ⟨669160800210243512481763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892214400280324683309017 669160800210243512481763)
                      ·
                        rfl

theorem cell23_1303186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_1303186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303186 prefixEnd_1303186 := by exact prefixLift 1303186
  have htrace : WordTrace (prefixWord ++ tailWord_1303186) baseStart_1303186 baseEnd_1303186 := by
    simpa [prefixWord, tailWord_1303186, baseEnd_1303186] using wordTrace_append hprefix tailTrace_1303186
  have hstable : (prefixWord ++ tailWord_1303186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303186).length < 2 ^ (prefixWord ++ tailWord_1303186).sum := by decide
  have hdescent : baseEnd_1303186 < baseStart_1303186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303192 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 4, 4]
def baseStart_1303192 : Nat := 118140960795 + 1303192 * 2 ^ 59
def prefixEnd_1303192 : Nat := 4983230072969 + 3 ^ 40 * 1303192 * 2
def baseEnd_1303192 : Nat := 223054627031390163002245

theorem tailTrace_1303192 : CollatzResearch.WordTrace tailWord_1303192 prefixEnd_1303192 223054627031390163002245 := by
  unfold tailWord_1303192
  simp only [CollatzResearch.WordTrace]
  refine ⟨23765658547382713159603915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31687544729843617546138553 23765658547382713159603915)
  ·
    refine ⟨35648487821074069739405873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23765658547382713159603915 35648487821074069739405873)
    ·
      refine ⟨26736365865805552304554405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35648487821074069739405873 26736365865805552304554405)
      ·
        refine ⟨5013068599838541057103951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26736365865805552304554405 5013068599838541057103951)
        ·
          refine ⟨7519602899757811585655927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5013068599838541057103951 7519602899757811585655927)
          ·
            refine ⟨11279404349636717378483891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519602899757811585655927 11279404349636717378483891)
            ·
              refine ⟨16919106524455076067725837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11279404349636717378483891 16919106524455076067725837)
              ·
                refine ⟨6344664946670653525397189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16919106524455076067725837 6344664946670653525397189)
                ·
                  refine ⟨1189624677500747536011973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6344664946670653525397189 1189624677500747536011973)
                  ·
                    refine ⟨223054627031390163002245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189624677500747536011973 223054627031390163002245)
                    ·
                      rfl

theorem cell23_1303192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_1303192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303192 prefixEnd_1303192 := by exact prefixLift 1303192
  have htrace : WordTrace (prefixWord ++ tailWord_1303192) baseStart_1303192 baseEnd_1303192 := by
    simpa [prefixWord, tailWord_1303192, baseEnd_1303192] using wordTrace_append hprefix tailTrace_1303192
  have hstable : (prefixWord ++ tailWord_1303192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303192).length < 2 ^ (prefixWord ++ tailWord_1303192).sum := by decide
  have hdescent : baseEnd_1303192 < baseStart_1303192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303219 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 3]
def baseStart_1303219 : Nat := 118140960795 + 1303219 * 2 ^ 59
def prefixEnd_1303219 : Nat := 4983230072969 + 3 ^ 40 * 1303219 * 2
def baseEnd_1303219 : Nat := 669177745071841883369111

theorem tailTrace_1303219 : CollatzResearch.WordTrace tailWord_1303219 prefixEnd_1303219 669177745071841883369111 := by
  unfold tailWord_1303219
  simp only [CollatzResearch.WordTrace]
  refine ⟨47532301865667609930440711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31688201243778406620293807 47532301865667609930440711)
  ·
    refine ⟨71298452798501414895661067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47532301865667609930440711 71298452798501414895661067)
    ·
      refine ⟨106947679197752122343491601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71298452798501414895661067 106947679197752122343491601)
      ·
        refine ⟨80210759398314091757618701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106947679197752122343491601 80210759398314091757618701)
        ·
          refine ⟨30079034774367784409107013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80210759398314091757618701 30079034774367784409107013)
          ·
            refine ⟨5639819020193959576707565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30079034774367784409107013 5639819020193959576707565)
            ·
              refine ⟨2114932132572734841265337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5639819020193959576707565 2114932132572734841265337)
              ·
                refine ⟨1586199099429551130949003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114932132572734841265337 1586199099429551130949003)
                ·
                  refine ⟨2379298649144326696423505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586199099429551130949003 2379298649144326696423505)
                  ·
                    refine ⟨1784473986858245022317629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2379298649144326696423505 1784473986858245022317629)
                    ·
                      refine ⟨669177745071841883369111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1784473986858245022317629 669177745071841883369111)
                      ·
                        rfl

theorem cell23_1303219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_1303219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303219 prefixEnd_1303219 := by exact prefixLift 1303219
  have htrace : WordTrace (prefixWord ++ tailWord_1303219) baseStart_1303219 baseEnd_1303219 := by
    simpa [prefixWord, tailWord_1303219, baseEnd_1303219] using wordTrace_append hprefix tailTrace_1303219
  have hstable : (prefixWord ++ tailWord_1303219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303219).length < 2 ^ (prefixWord ++ tailWord_1303219).sum := by decide
  have hdescent : baseEnd_1303219 < baseStart_1303219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303232 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_1303232 : Nat := 118140960795 + 1303232 * 2 ^ 59
def prefixEnd_1303232 : Nat := 4983230072969 + 3 ^ 40 * 1303232 * 2
def baseEnd_1303232 : Nat := 669184420320350332506551

theorem tailTrace_1303232 : CollatzResearch.WordTrace tailWord_1303232 prefixEnd_1303232 669184420320350332506551 := by
  unfold tailWord_1303232
  simp only [CollatzResearch.WordTrace]
  refine ⟨23766388007310256575331975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31688517343080342100442633 23766388007310256575331975)
  ·
    refine ⟨35649582010965384862997963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23766388007310256575331975 35649582010965384862997963)
    ·
      refine ⟨53474373016448077294496945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35649582010965384862997963 53474373016448077294496945)
      ·
        refine ⟨40105779762336057970872709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53474373016448077294496945 40105779762336057970872709)
        ·
          refine ⟨7519833705438010869538633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40105779762336057970872709 7519833705438010869538633)
          ·
            refine ⟨5639875279078508152153975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7519833705438010869538633 5639875279078508152153975)
            ·
              refine ⟨8459812918617762228230963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639875279078508152153975 8459812918617762228230963)
              ·
                refine ⟨12689719377926643342346445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8459812918617762228230963 12689719377926643342346445)
                ·
                  refine ⟨4758644766722491253379917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12689719377926643342346445 4758644766722491253379917)
                  ·
                    refine ⟨1784491787520934220017469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4758644766722491253379917 1784491787520934220017469)
                    ·
                      refine ⟨669184420320350332506551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1784491787520934220017469 669184420320350332506551)
                      ·
                        rfl

theorem cell23_1303232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_1303232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303232 prefixEnd_1303232 := by exact prefixLift 1303232
  have htrace : WordTrace (prefixWord ++ tailWord_1303232) baseStart_1303232 baseEnd_1303232 := by
    simpa [prefixWord, tailWord_1303232, baseEnd_1303232] using wordTrace_append hprefix tailTrace_1303232
  have hstable : (prefixWord ++ tailWord_1303232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303232).length < 2 ^ (prefixWord ++ tailWord_1303232).sum := by decide
  have hdescent : baseEnd_1303232 < baseStart_1303232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303250 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1303250 : Nat := 118140960795 + 1303250 * 2 ^ 59
def prefixEnd_1303250 : Nat := 4983230072969 + 3 ^ 40 * 1303250 * 2
def baseEnd_1303250 : Nat := 669193662972131262081469

theorem tailTrace_1303250 : CollatzResearch.WordTrace tailWord_1303250 prefixEnd_1303250 669193662972131262081469 := by
  unfold tailWord_1303250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883358132138825556204801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31688955019036868149879469 11883358132138825556204801)
  ·
    refine ⟨8912518599104119167153601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11883358132138825556204801 8912518599104119167153601)
    ·
      refine ⟨6684388949328089375365201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8912518599104119167153601 6684388949328089375365201)
      ·
        refine ⟨5013291711996067031523901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6684388949328089375365201 5013291711996067031523901)
        ·
          refine ⟨1879984391998525136821463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5013291711996067031523901 1879984391998525136821463)
          ·
            refine ⟨2819976587997787705232195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879984391998525136821463 2819976587997787705232195)
            ·
              refine ⟨4229964881996681557848293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819976587997787705232195 4229964881996681557848293)
              ·
                refine ⟨793118415374377792096555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4229964881996681557848293 793118415374377792096555)
                ·
                  refine ⟨1189677623061566688144833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793118415374377792096555 1189677623061566688144833)
                  ·
                    refine ⟨892258217296175016108625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189677623061566688144833 892258217296175016108625)
                    ·
                      refine ⟨669193662972131262081469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892258217296175016108625 669193662972131262081469)
                      ·
                        rfl

theorem cell23_1303250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1303250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303250 prefixEnd_1303250 := by exact prefixLift 1303250
  have htrace : WordTrace (prefixWord ++ tailWord_1303250) baseStart_1303250 baseEnd_1303250 := by
    simpa [prefixWord, tailWord_1303250, baseEnd_1303250] using wordTrace_append hprefix tailTrace_1303250
  have hstable : (prefixWord ++ tailWord_1303250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303250).length < 2 ^ (prefixWord ++ tailWord_1303250).sum := by decide
  have hdescent : baseEnd_1303250 < baseStart_1303250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303284 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1303284 : Nat := 118140960795 + 1303284 * 2 ^ 59
def prefixEnd_1303284 : Nat := 4983230072969 + 3 ^ 40 * 1303284 * 2
def baseEnd_1303284 : Nat := 669211121314384129056313

theorem tailTrace_1303284 : CollatzResearch.WordTrace tailWord_1303284 prefixEnd_1303284 669211121314384129056313 := by
  unfold tailWord_1303284
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767336305216063015778453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31689781740288084021037937 23767336305216063015778453)
  ·
    refine ⟨1114093889307002953864615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23767336305216063015778453 1114093889307002953864615)
    ·
      refine ⟨1671140833960504430796923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114093889307002953864615 1671140833960504430796923)
      ·
        refine ⟨2506711250940756646195385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671140833960504430796923 2506711250940756646195385)
        ·
          refine ⟨1880033438205567484646539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2506711250940756646195385 1880033438205567484646539)
          ·
            refine ⟨2820050157308351226969809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880033438205567484646539 2820050157308351226969809)
            ·
              refine ⟨2115037617981263420227357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820050157308351226969809 2115037617981263420227357)
              ·
                refine ⟨793139106742973782585259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2115037617981263420227357 793139106742973782585259)
                ·
                  refine ⟨1189708660114460673877889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793139106742973782585259 1189708660114460673877889)
                  ·
                    refine ⟨892281495085845505408417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189708660114460673877889 892281495085845505408417)
                    ·
                      refine ⟨669211121314384129056313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892281495085845505408417 669211121314384129056313)
                      ·
                        rfl

theorem cell23_1303284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1303284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303284 prefixEnd_1303284 := by exact prefixLift 1303284
  have htrace : WordTrace (prefixWord ++ tailWord_1303284) baseStart_1303284 baseEnd_1303284 := by
    simpa [prefixWord, tailWord_1303284, baseEnd_1303284] using wordTrace_append hprefix tailTrace_1303284
  have hstable : (prefixWord ++ tailWord_1303284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303284).length < 2 ^ (prefixWord ++ tailWord_1303284).sum := by decide
  have hdescent : baseEnd_1303284 < baseStart_1303284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303295 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 11]
def baseStart_1303295 : Nat := 118140960795 + 1303295 * 2 ^ 59
def prefixEnd_1303295 : Nat := 4983230072969 + 3 ^ 40 * 1303295 * 2
def baseEnd_1303295 : Nat := 74357418844620398446529

theorem tailTrace_1303295 : CollatzResearch.WordTrace tailWord_1303295 prefixEnd_1303295 74357418844620398446529 := by
  unfold tailWord_1303295
  simp only [CollatzResearch.WordTrace]
  refine ⟨47535073813392274910207339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31690049208928183273471559 47535073813392274910207339)
  ·
    refine ⟨71302610720088412365311009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47535073813392274910207339 71302610720088412365311009)
    ·
      refine ⟨53476958040066309273983257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71302610720088412365311009 53476958040066309273983257)
      ·
        refine ⟨40107718530049731955487443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53476958040066309273983257 40107718530049731955487443)
        ·
          refine ⟨60161577795074597933231165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40107718530049731955487443 60161577795074597933231165)
          ·
            refine ⟨22560591673152974224961687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60161577795074597933231165 22560591673152974224961687)
            ·
              refine ⟨33840887509729461337442531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22560591673152974224961687 33840887509729461337442531)
              ·
                refine ⟨50761331264594192006163797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33840887509729461337442531 50761331264594192006163797)
                ·
                  refine ⟨74357418844620398446529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 50761331264594192006163797 74357418844620398446529)
                  ·
                    rfl

theorem cell23_1303295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 11].length) (baseStart_1303295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303295 prefixEnd_1303295 := by exact prefixLift 1303295
  have htrace : WordTrace (prefixWord ++ tailWord_1303295) baseStart_1303295 baseEnd_1303295 := by
    simpa [prefixWord, tailWord_1303295, baseEnd_1303295] using wordTrace_append hprefix tailTrace_1303295
  have hstable : (prefixWord ++ tailWord_1303295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303295).length < 2 ^ (prefixWord ++ tailWord_1303295).sum := by decide
  have hdescent : baseEnd_1303295 < baseStart_1303295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303306 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_1303306 : Nat := 118140960795 + 1303306 * 2 ^ 59
def prefixEnd_1303306 : Nat := 4983230072969 + 3 ^ 40 * 1303306 * 2
def baseEnd_1303306 : Nat := 669222417888783042981211

theorem tailTrace_1303306 : CollatzResearch.WordTrace tailWord_1303306 prefixEnd_1303306 669222417888783042981211 := by
  unfold tailWord_1303306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883868754088105947214443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31690316677568282525905181 11883868754088105947214443)
  ·
    refine ⟨17825803131132158920821665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11883868754088105947214443 17825803131132158920821665)
    ·
      refine ⟨13369352348349119190616249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17825803131132158920821665 13369352348349119190616249)
      ·
        refine ⟨10027014261261839392962187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13369352348349119190616249 10027014261261839392962187)
        ·
          refine ⟨15040521391892759089443281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10027014261261839392962187 15040521391892759089443281)
          ·
            refine ⟨11280391043919569317082461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15040521391892759089443281 11280391043919569317082461)
            ·
              refine ⟨4230146641469838493905923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11280391043919569317082461 4230146641469838493905923)
              ·
                refine ⟨6345219962204757740858885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230146641469838493905923 6345219962204757740858885)
                ·
                  refine ⟨1189728742913392076411041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6345219962204757740858885 1189728742913392076411041)
                  ·
                    refine ⟨892296557185044057308281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189728742913392076411041 892296557185044057308281)
                    ·
                      refine ⟨669222417888783042981211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892296557185044057308281 669222417888783042981211)
                      ·
                        rfl

theorem cell23_1303306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_1303306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303306 prefixEnd_1303306 := by exact prefixLift 1303306
  have htrace : WordTrace (prefixWord ++ tailWord_1303306) baseStart_1303306 baseEnd_1303306 := by
    simpa [prefixWord, tailWord_1303306, baseEnd_1303306] using wordTrace_append hprefix tailTrace_1303306
  have hstable : (prefixWord ++ tailWord_1303306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303306).length < 2 ^ (prefixWord ++ tailWord_1303306).sum := by decide
  have hdescent : baseEnd_1303306 < baseStart_1303306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303352 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1303352 : Nat := 118140960795 + 1303352 * 2 ^ 59
def prefixEnd_1303352 : Nat := 4983230072969 + 3 ^ 40 * 1303352 * 2
def baseEnd_1303352 : Nat := 669246037998889863005999

theorem tailTrace_1303352 : CollatzResearch.WordTrace tailWord_1303352 prefixEnd_1303352 669246037998889863005999 := by
  unfold tailWord_1303352
  simp only [CollatzResearch.WordTrace]
  refine ⟨23768576387092886822516155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31691435182790515763354873 23768576387092886822516155)
  ·
    refine ⟨35652864580639330233774233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23768576387092886822516155 35652864580639330233774233)
    ·
      refine ⟨26739648435479497675330675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35652864580639330233774233 26739648435479497675330675)
      ·
        refine ⟨40109472653219246512996013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26739648435479497675330675 40109472653219246512996013)
        ·
          refine ⟨15041052244957217442373505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40109472653219246512996013 15041052244957217442373505)
          ·
            refine ⟨11280789183717913081780129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15041052244957217442373505 11280789183717913081780129)
            ·
              refine ⟨8460591887788434811335097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11280789183717913081780129 8460591887788434811335097)
              ·
                refine ⟨6345443915841326108501323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8460591887788434811335097 6345443915841326108501323)
                ·
                  refine ⟨9518165873761989162751985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6345443915841326108501323 9518165873761989162751985)
                  ·
                    refine ⟨7138624405321491872063989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9518165873761989162751985 7138624405321491872063989)
                    ·
                      refine ⟨669246037998889863005999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7138624405321491872063989 669246037998889863005999)
                      ·
                        rfl

theorem cell23_1303352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1303352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303352 prefixEnd_1303352 := by exact prefixLift 1303352
  have htrace : WordTrace (prefixWord ++ tailWord_1303352) baseStart_1303352 baseEnd_1303352 := by
    simpa [prefixWord, tailWord_1303352, baseEnd_1303352] using wordTrace_append hprefix tailTrace_1303352
  have hstable : (prefixWord ++ tailWord_1303352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303352).length < 2 ^ (prefixWord ++ tailWord_1303352).sum := by decide
  have hdescent : baseEnd_1303352 < baseStart_1303352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303359 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 2, 5]
def baseStart_1303359 : Nat := 118140960795 + 1303359 * 2 ^ 59
def prefixEnd_1303359 : Nat := 4983230072969 + 3 ^ 40 * 1303359 * 2
def baseEnd_1303359 : Nat := 223083210787823778539489

theorem tailTrace_1303359 : CollatzResearch.WordTrace tailWord_1303359 prefixEnd_1303359 223083210787823778539489 := by
  unfold tailWord_1303359
  simp only [CollatzResearch.WordTrace]
  refine ⟨47537408085160413840537131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31691605390106942560358087 47537408085160413840537131)
  ·
    refine ⟨71306112127740620760805697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47537408085160413840537131 71306112127740620760805697)
    ·
      refine ⟨53479584095805465570604273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71306112127740620760805697 53479584095805465570604273)
      ·
        refine ⟨40109688071854099177953205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53479584095805465570604273 40109688071854099177953205)
        ·
          refine ⟨3760283256736321797933113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40109688071854099177953205 3760283256736321797933113)
          ·
            refine ⟨2820212442552241348449835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3760283256736321797933113 2820212442552241348449835)
            ·
              refine ⟨4230318663828362022674753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820212442552241348449835 4230318663828362022674753)
              ·
                refine ⟨3172738997871271517006065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4230318663828362022674753 3172738997871271517006065)
                ·
                  refine ⟨2379554248403453637754549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172738997871271517006065 2379554248403453637754549)
                  ·
                    refine ⟨223083210787823778539489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2379554248403453637754549 223083210787823778539489)
                    ·
                      rfl

theorem cell23_1303359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_1303359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303359 prefixEnd_1303359 := by exact prefixLift 1303359
  have htrace : WordTrace (prefixWord ++ tailWord_1303359) baseStart_1303359 baseEnd_1303359 := by
    simpa [prefixWord, tailWord_1303359, baseEnd_1303359] using wordTrace_append hprefix tailTrace_1303359
  have hstable : (prefixWord ++ tailWord_1303359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303359).length < 2 ^ (prefixWord ++ tailWord_1303359).sum := by decide
  have hdescent : baseEnd_1303359 < baseStart_1303359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303379 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 2, 4, 2]
def baseStart_1303379 : Nat := 118140960795 + 1303379 * 2 ^ 59
def prefixEnd_1303379 : Nat := 4983230072969 + 3 ^ 40 * 1303379 * 2
def baseEnd_1303379 : Nat := 669259901976561257368375

theorem tailTrace_1303379 : CollatzResearch.WordTrace tailWord_1303379 prefixEnd_1303379 669259901976561257368375 := by
  unfold tailWord_1303379
  simp only [CollatzResearch.WordTrace]
  refine ⟨47538137545087957256265191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31692091696725304837510127 47538137545087957256265191)
  ·
    refine ⟨71307206317631935884397787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47538137545087957256265191 71307206317631935884397787)
    ·
      refine ⟨106960809476447903826596681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71307206317631935884397787 106960809476447903826596681)
      ·
        refine ⟨80220607107335927869947511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106960809476447903826596681 80220607107335927869947511)
        ·
          refine ⟨120330910661003891804921267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80220607107335927869947511 120330910661003891804921267)
          ·
            refine ⟨180496365991505837707381901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120330910661003891804921267 180496365991505837707381901)
            ·
              refine ⟨67686137246814689140268213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180496365991505837707381901 67686137246814689140268213)
              ·
                refine ⟨6345575366888877106900145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67686137246814689140268213 6345575366888877106900145)
                ·
                  refine ⟨4759181525166657830175109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6345575366888877106900145 4759181525166657830175109)
                  ·
                    refine ⟨892346535968748343157833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759181525166657830175109 892346535968748343157833)
                    ·
                      refine ⟨669259901976561257368375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892346535968748343157833 669259901976561257368375)
                      ·
                        rfl

theorem cell23_1303379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 4, 2].length) (baseStart_1303379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303379 prefixEnd_1303379 := by exact prefixLift 1303379
  have htrace : WordTrace (prefixWord ++ tailWord_1303379) baseStart_1303379 baseEnd_1303379 := by
    simpa [prefixWord, tailWord_1303379, baseEnd_1303379] using wordTrace_append hprefix tailTrace_1303379
  have hstable : (prefixWord ++ tailWord_1303379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303379).length < 2 ^ (prefixWord ++ tailWord_1303379).sum := by decide
  have hdescent : baseEnd_1303379 < baseStart_1303379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303396 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_1303396 : Nat := 118140960795 + 1303396 * 2 ^ 59
def prefixEnd_1303396 : Nat := 4983230072969 + 3 ^ 40 * 1303396 * 2
def baseEnd_1303396 : Nat := 669268631147687690855797

theorem tailTrace_1303396 : CollatzResearch.WordTrace tailWord_1303396 prefixEnd_1303396 669268631147687690855797 := by
  unfold tailWord_1303396
  simp only [CollatzResearch.WordTrace]
  refine ⟨23769378793013184579817021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31692505057350912773089361 23769378793013184579817021)
  ·
    refine ⟨8913517047379944217431383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23769378793013184579817021 8913517047379944217431383)
    ·
      refine ⟨13370275571069916326147075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8913517047379944217431383 13370275571069916326147075)
      ·
        refine ⟨20055413356604874489220613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13370275571069916326147075 20055413356604874489220613)
        ·
          refine ⟨3760390004363413966728865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20055413356604874489220613 3760390004363413966728865)
          ·
            refine ⟨2820292503272560475046649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3760390004363413966728865 2820292503272560475046649)
            ·
              refine ⟨2115219377454420356284987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820292503272560475046649 2115219377454420356284987)
              ·
                refine ⟨3172829066181630534427481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115219377454420356284987 3172829066181630534427481)
                ·
                  refine ⟨2379621799636222900820611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172829066181630534427481 2379621799636222900820611)
                  ·
                    refine ⟨3569432699454334351230917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2379621799636222900820611 3569432699454334351230917)
                    ·
                      refine ⟨669268631147687690855797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3569432699454334351230917 669268631147687690855797)
                      ·
                        rfl

theorem cell23_1303396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_1303396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303396 prefixEnd_1303396 := by exact prefixLift 1303396
  have htrace : WordTrace (prefixWord ++ tailWord_1303396) baseStart_1303396 baseEnd_1303396 := by
    simpa [prefixWord, tailWord_1303396, baseEnd_1303396] using wordTrace_append hprefix tailTrace_1303396
  have hstable : (prefixWord ++ tailWord_1303396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303396).length < 2 ^ (prefixWord ++ tailWord_1303396).sum := by decide
  have hdescent : baseEnd_1303396 < baseStart_1303396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303423 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 1, 4]
def baseStart_1303423 : Nat := 118140960795 + 1303423 * 2 ^ 59
def prefixEnd_1303423 : Nat := 4983230072969 + 3 ^ 40 * 1303423 * 2
def baseEnd_1303423 : Nat := 223094165041786361739391

theorem tailTrace_1303423 : CollatzResearch.WordTrace tailWord_1303423 prefixEnd_1303423 223094165041786361739391 := by
  unfold tailWord_1303423
  simp only [CollatzResearch.WordTrace]
  refine ⟨47539742356928552770866923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31693161571285701847244615 47539742356928552770866923)
  ·
    refine ⟨71309613535392829156300385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47539742356928552770866923 71309613535392829156300385)
    ·
      refine ⟨53482210151544621867225289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71309613535392829156300385 53482210151544621867225289)
      ·
        refine ⟨40111657613658466400418967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53482210151544621867225289 40111657613658466400418967)
        ·
          refine ⟨60167486420487699600628451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40111657613658466400418967 60167486420487699600628451)
          ·
            refine ⟨90251229630731549400942677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60167486420487699600628451 90251229630731549400942677)
            ·
              refine ⟨1057631597235135344542297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 90251229630731549400942677 1057631597235135344542297)
              ·
                refine ⟨793223697926351508406723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1057631597235135344542297 793223697926351508406723)
                ·
                  refine ⟨1189835546889527262610085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793223697926351508406723 1189835546889527262610085)
                  ·
                    refine ⟨223094165041786361739391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1189835546889527262610085 223094165041786361739391)
                    ·
                      rfl

theorem cell23_1303423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 4].length) (baseStart_1303423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303423 prefixEnd_1303423 := by exact prefixLift 1303423
  have htrace : WordTrace (prefixWord ++ tailWord_1303423) baseStart_1303423 baseEnd_1303423 := by
    simpa [prefixWord, tailWord_1303423, baseEnd_1303423] using wordTrace_append hprefix tailTrace_1303423
  have hstable : (prefixWord ++ tailWord_1303423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303423).length < 2 ^ (prefixWord ++ tailWord_1303423).sum := by decide
  have hdescent : baseEnd_1303423 < baseStart_1303423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303449 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 1, 5]
def baseStart_1303449 : Nat := 118140960795 + 1303449 * 2 ^ 59
def prefixEnd_1303449 : Nat := 4983230072969 + 3 ^ 40 * 1303449 * 2
def baseEnd_1303449 : Nat := 223098615207458661164351

theorem tailTrace_1303449 : CollatzResearch.WordTrace tailWord_1303449 prefixEnd_1303449 223098615207458661164351 := by
  unfold tailWord_1303449
  simp only [CollatzResearch.WordTrace]
  refine ⟨47540690654834359211313401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31693793769889572807542267 47540690654834359211313401)
  ·
    refine ⟨35655517991125769408485051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47540690654834359211313401 35655517991125769408485051)
    ·
      refine ⟨53483276986688654112727577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35655517991125769408485051 53483276986688654112727577)
      ·
        refine ⟨40112457740016490584545683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53483276986688654112727577 40112457740016490584545683)
        ·
          refine ⟨60168686610024735876818525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40112457740016490584545683 60168686610024735876818525)
          ·
            refine ⟨22563257478759275953806947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60168686610024735876818525 22563257478759275953806947)
            ·
              refine ⟨33844886218138913930710421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22563257478759275953806947 33844886218138913930710421)
              ·
                refine ⟨1586479041475261590502051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33844886218138913930710421 1586479041475261590502051)
                ·
                  refine ⟨2379718562212892385753077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586479041475261590502051 2379718562212892385753077)
                  ·
                    refine ⟨223098615207458661164351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2379718562212892385753077 223098615207458661164351)
                    ·
                      rfl

theorem cell23_1303449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_1303449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303449 prefixEnd_1303449 := by exact prefixLift 1303449
  have htrace : WordTrace (prefixWord ++ tailWord_1303449) baseStart_1303449 baseEnd_1303449 := by
    simpa [prefixWord, tailWord_1303449, baseEnd_1303449] using wordTrace_append hprefix tailTrace_1303449
  have hstable : (prefixWord ++ tailWord_1303449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303449).length < 2 ^ (prefixWord ++ tailWord_1303449).sum := by decide
  have hdescent : baseEnd_1303449 < baseStart_1303449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303450 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3]
def baseStart_1303450 : Nat := 118140960795 + 1303450 * 2 ^ 59
def prefixEnd_1303450 : Nat := 4983230072969 + 3 ^ 40 * 1303450 * 2
def baseEnd_1303450 : Nat := 669296359103030479580549

theorem tailTrace_1303450 : CollatzResearch.WordTrace tailWord_1303450 prefixEnd_1303450 669296359103030479580549 := by
  unfold tailWord_1303450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11885181781957684095524951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31693818085220490921399869 11885181781957684095524951)
  ·
    refine ⟨17827772672936526143287427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11885181781957684095524951 17827772672936526143287427)
    ·
      refine ⟨26741659009404789214931141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17827772672936526143287427 26741659009404789214931141)
      ·
        refine ⟨5014061064263397977799589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26741659009404789214931141 5014061064263397977799589)
        ·
          refine ⟨940136449549387120837423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5014061064263397977799589 940136449549387120837423)
          ·
            refine ⟨1410204674324080681256135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940136449549387120837423 1410204674324080681256135)
            ·
              refine ⟨2115307011486121021884203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410204674324080681256135 2115307011486121021884203)
              ·
                refine ⟨3172960517229181532826305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115307011486121021884203 3172960517229181532826305)
                ·
                  refine ⟨2379720387921886149619729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3172960517229181532826305 2379720387921886149619729)
                  ·
                    refine ⟨1784790290941414612214797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2379720387921886149619729 1784790290941414612214797)
                    ·
                      refine ⟨669296359103030479580549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1784790290941414612214797 669296359103030479580549)
                      ·
                        rfl

theorem cell23_1303450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_1303450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303450 prefixEnd_1303450 := by exact prefixLift 1303450
  have htrace : WordTrace (prefixWord ++ tailWord_1303450) baseStart_1303450 baseEnd_1303450 := by
    simpa [prefixWord, tailWord_1303450, baseEnd_1303450] using wordTrace_append hprefix tailTrace_1303450
  have hstable : (prefixWord ++ tailWord_1303450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303450).length < 2 ^ (prefixWord ++ tailWord_1303450).sum := by decide
  have hdescent : baseEnd_1303450 < baseStart_1303450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303499 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6]
def baseStart_1303499 : Nat := 118140960795 + 1303499 * 2 ^ 59
def prefixEnd_1303499 : Nat := 4983230072969 + 3 ^ 40 * 1303499 * 2
def baseEnd_1303499 : Nat := 669321519655100787867823

theorem tailTrace_1303499 : CollatzResearch.WordTrace tailWord_1303499 prefixEnd_1303499 669321519655100787867823 := by
  unfold tailWord_1303499
  simp only [CollatzResearch.WordTrace]
  refine ⟨47542514304653217750633551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31695009536435478500422367 47542514304653217750633551)
  ·
    refine ⟨71313771456979826625950327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47542514304653217750633551 71313771456979826625950327)
    ·
      refine ⟨106970657185469739938925491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71313771456979826625950327 106970657185469739938925491)
      ·
        refine ⟨160455985778204609908388237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106970657185469739938925491 160455985778204609908388237)
        ·
          refine ⟨60170994666826728715645589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160455985778204609908388237 60170994666826728715645589)
          ·
            refine ⟨2820515375007502908545887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60170994666826728715645589 2820515375007502908545887)
            ·
              refine ⟨4230773062511254362818831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820515375007502908545887 4230773062511254362818831)
              ·
                refine ⟨6346159593766881544228247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230773062511254362818831 6346159593766881544228247)
                ·
                  refine ⟨9519239390650322316342371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6346159593766881544228247 9519239390650322316342371)
                  ·
                    refine ⟨14278859085975483474513557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9519239390650322316342371 14278859085975483474513557)
                    ·
                      refine ⟨669321519655100787867823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14278859085975483474513557 669321519655100787867823)
                      ·
                        rfl

theorem cell23_1303499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].length) (baseStart_1303499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303499 prefixEnd_1303499 := by exact prefixLift 1303499
  have htrace : WordTrace (prefixWord ++ tailWord_1303499) baseStart_1303499 baseEnd_1303499 := by
    simpa [prefixWord, tailWord_1303499, baseEnd_1303499] using wordTrace_append hprefix tailTrace_1303499
  have hstable : (prefixWord ++ tailWord_1303499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303499).length < 2 ^ (prefixWord ++ tailWord_1303499).sum := by decide
  have hdescent : baseEnd_1303499 < baseStart_1303499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303503 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 3, 2, 2]
def baseStart_1303503 : Nat := 118140960795 + 1303503 * 2 ^ 59
def prefixEnd_1303503 : Nat := 4983230072969 + 3 ^ 40 * 1303503 * 2
def baseEnd_1303503 : Nat := 669323573577718772217805

theorem tailTrace_1303503 : CollatzResearch.WordTrace tailWord_1303503 prefixEnd_1303503 669323573577718772217805 := by
  unfold tailWord_1303503
  simp only [CollatzResearch.WordTrace]
  refine ⟨47542660196638726433779163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31695106797759150955852775 47542660196638726433779163)
  ·
    refine ⟨71313990294958089650668745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47542660196638726433779163 71313990294958089650668745)
    ·
      refine ⟨53485492721218567238001559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71313990294958089650668745 53485492721218567238001559)
      ·
        refine ⟨80228239081827850857002339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53485492721218567238001559 80228239081827850857002339)
        ·
          refine ⟨120342358622741776285503509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80228239081827850857002339 120342358622741776285503509)
          ·
            refine ⟨5641048060441020763382977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120342358622741776285503509 5641048060441020763382977)
            ·
              refine ⟨4230786045330765572537233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5641048060441020763382977 4230786045330765572537233)
              ·
                refine ⟨3173089533998074179402925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4230786045330765572537233 3173089533998074179402925)
                ·
                  refine ⟨1189908575249277817276097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3173089533998074179402925 1189908575249277817276097)
                  ·
                    refine ⟨892431431436958362957073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1189908575249277817276097 892431431436958362957073)
                    ·
                      refine ⟨669323573577718772217805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892431431436958362957073 669323573577718772217805)
                      ·
                        rfl

theorem cell23_1303503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 2, 2].length) (baseStart_1303503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303503 prefixEnd_1303503 := by exact prefixLift 1303503
  have htrace : WordTrace (prefixWord ++ tailWord_1303503) baseStart_1303503 baseEnd_1303503 := by
    simpa [prefixWord, tailWord_1303503, baseEnd_1303503] using wordTrace_append hprefix tailTrace_1303503
  have hstable : (prefixWord ++ tailWord_1303503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303503).length < 2 ^ (prefixWord ++ tailWord_1303503).sum := by decide
  have hdescent : baseEnd_1303503 < baseStart_1303503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303554 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1303554 : Nat := 118140960795 + 1303554 * 2 ^ 59
def prefixEnd_1303554 : Nat := 4983230072969 + 3 ^ 40 * 1303554 * 2
def baseEnd_1303554 : Nat := 669349761091098072680071

theorem tailTrace_1303554 : CollatzResearch.WordTrace tailWord_1303554 prefixEnd_1303554 669349761091098072680071 := by
  unfold tailWord_1303554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886130079863490535971429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31696346879635974762590477 11886130079863490535971429)
  ·
    refine ⟨2228649389974404475494643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11886130079863490535971429 2228649389974404475494643)
    ·
      refine ⟨3342974084961606713241965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228649389974404475494643 3342974084961606713241965)
      ·
        refine ⟨1253615281860602517465737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3342974084961606713241965 1253615281860602517465737)
        ·
          refine ⟨940211461395451888099303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253615281860602517465737 940211461395451888099303)
          ·
            refine ⟨1410317192093177832148955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940211461395451888099303 1410317192093177832148955)
            ·
              refine ⟨2115475788139766748223433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410317192093177832148955 2115475788139766748223433)
              ·
                refine ⟨1586606841104825061167575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2115475788139766748223433 1586606841104825061167575)
                ·
                  refine ⟨2379910261657237591751363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586606841104825061167575 2379910261657237591751363)
                  ·
                    refine ⟨3569865392485856387627045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2379910261657237591751363 3569865392485856387627045)
                    ·
                      refine ⟨669349761091098072680071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3569865392485856387627045 669349761091098072680071)
                      ·
                        rfl

theorem cell23_1303554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1303554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303554 prefixEnd_1303554 := by exact prefixLift 1303554
  have htrace : WordTrace (prefixWord ++ tailWord_1303554) baseStart_1303554 baseEnd_1303554 := by
    simpa [prefixWord, tailWord_1303554, baseEnd_1303554] using wordTrace_append hprefix tailTrace_1303554
  have hstable : (prefixWord ++ tailWord_1303554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303554).length < 2 ^ (prefixWord ++ tailWord_1303554).sum := by decide
  have hdescent : baseEnd_1303554 < baseStart_1303554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303563 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 3, 3, 2]
def baseStart_1303563 : Nat := 118140960795 + 1303563 * 2 ^ 59
def prefixEnd_1303563 : Nat := 4983230072969 + 3 ^ 40 * 1303563 * 2
def baseEnd_1303563 : Nat := 669354382416988537467529

theorem tailTrace_1303563 : CollatzResearch.WordTrace tailWord_1303563 prefixEnd_1303563 669354382416988537467529 := by
  unfold tailWord_1303563
  simp only [CollatzResearch.WordTrace]
  refine ⟨47544848576421356680963343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31696565717614237787308895 47544848576421356680963343)
  ·
    refine ⟨71317272864632035021445015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47544848576421356680963343 71317272864632035021445015)
    ·
      refine ⟨106975909296948052532167523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71317272864632035021445015 106975909296948052532167523)
      ·
        refine ⟨160463863945422078798251285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106975909296948052532167523 160463863945422078798251285)
        ·
          refine ⟨7521743622441659943668029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160463863945422078798251285 7521743622441659943668029)
          ·
            refine ⟨2820653858415622478875511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7521743622441659943668029 2820653858415622478875511)
            ·
              refine ⟨4230980787623433718313267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820653858415622478875511 4230980787623433718313267)
              ·
                refine ⟨6346471181435150577469901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230980787623433718313267 6346471181435150577469901)
                ·
                  refine ⟨2379926693038181466551213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6346471181435150577469901 2379926693038181466551213)
                  ·
                    refine ⟨892472509889318049956705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379926693038181466551213 892472509889318049956705)
                    ·
                      refine ⟨669354382416988537467529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892472509889318049956705 669354382416988537467529)
                      ·
                        rfl

theorem cell23_1303563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3, 2].length) (baseStart_1303563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303563 prefixEnd_1303563 := by exact prefixLift 1303563
  have htrace : WordTrace (prefixWord ++ tailWord_1303563) baseStart_1303563 baseEnd_1303563 := by
    simpa [prefixWord, tailWord_1303563, baseEnd_1303563] using wordTrace_append hprefix tailTrace_1303563
  have hstable : (prefixWord ++ tailWord_1303563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303563).length < 2 ^ (prefixWord ++ tailWord_1303563).sum := by decide
  have hdescent : baseEnd_1303563 < baseStart_1303563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303610 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2]
def baseStart_1303610 : Nat := 118140960795 + 1303610 * 2 ^ 59
def prefixEnd_1303610 : Nat := 4983230072969 + 3 ^ 40 * 1303610 * 2
def baseEnd_1303610 : Nat := 669378516007749853579813

theorem tailTrace_1303610 : CollatzResearch.WordTrace tailWord_1303610 prefixEnd_1303610 669378516007749853579813 := by
  unfold tailWord_1303610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886640701812770926981071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31697708538167389138616189 11886640701812770926981071)
  ·
    refine ⟨17829961052719156390471607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11886640701812770926981071 17829961052719156390471607)
    ·
      refine ⟨26744941579078734585707411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17829961052719156390471607 26744941579078734585707411)
      ·
        refine ⟨40117412368618101878561117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26744941579078734585707411 40117412368618101878561117)
        ·
          refine ⟨15044029638231788204460419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40117412368618101878561117 15044029638231788204460419)
          ·
            refine ⟨22566044457347682306690629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15044029638231788204460419 22566044457347682306690629)
            ·
              refine ⟨4231133335752690432504493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22566044457347682306690629 4231133335752690432504493)
              ·
                refine ⟨1586675000907258912189185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4231133335752690432504493 1586675000907258912189185)
                ·
                  refine ⟨1190006250680444184141889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1586675000907258912189185 1190006250680444184141889)
                  ·
                    refine ⟨892504688010333138106417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1190006250680444184141889 892504688010333138106417)
                    ·
                      refine ⟨669378516007749853579813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892504688010333138106417 669378516007749853579813)
                      ·
                        rfl

theorem cell23_1303610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_1303610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303610 prefixEnd_1303610 := by exact prefixLift 1303610
  have htrace : WordTrace (prefixWord ++ tailWord_1303610) baseStart_1303610 baseEnd_1303610 := by
    simpa [prefixWord, tailWord_1303610, baseEnd_1303610] using wordTrace_append hprefix tailTrace_1303610
  have hstable : (prefixWord ++ tailWord_1303610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303610).length < 2 ^ (prefixWord ++ tailWord_1303610).sum := by decide
  have hdescent : baseEnd_1303610 < baseStart_1303610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303650 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1303650 : Nat := 118140960795 + 1303650 * 2 ^ 59
def prefixEnd_1303650 : Nat := 4983230072969 + 3 ^ 40 * 1303650 * 2
def baseEnd_1303650 : Nat := 74377672803769966342181

theorem tailTrace_1303650 : CollatzResearch.WordTrace tailWord_1303650 prefixEnd_1303650 74377672803769966342181 := by
  unfold tailWord_1303650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887005431776542634845101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31698681151404113692920269 11887005431776542634845101)
  ·
    refine ⟨4457627036916203488066913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11887005431776542634845101 4457627036916203488066913)
    ·
      refine ⟨3343220277687152616050185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4457627036916203488066913 3343220277687152616050185)
      ·
        refine ⟨2507415208265364462037639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3343220277687152616050185 2507415208265364462037639)
        ·
          refine ⟨3761122812398046693056459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507415208265364462037639 3761122812398046693056459)
          ·
            refine ⟨5641684218597070039584689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761122812398046693056459 5641684218597070039584689)
            ·
              refine ⟨4231263163947802529688517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5641684218597070039584689 4231263163947802529688517)
              ·
                refine ⟨793361843240212974316597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4231263163947802529688517 793361843240212974316597)
                ·
                  refine ⟨74377672803769966342181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793361843240212974316597 74377672803769966342181)
                  ·
                    rfl

theorem cell23_1303650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1303650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303650 prefixEnd_1303650 := by exact prefixLift 1303650
  have htrace : WordTrace (prefixWord ++ tailWord_1303650) baseStart_1303650 baseEnd_1303650 := by
    simpa [prefixWord, tailWord_1303650, baseEnd_1303650] using wordTrace_append hprefix tailTrace_1303650
  have hstable : (prefixWord ++ tailWord_1303650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303650).length < 2 ^ (prefixWord ++ tailWord_1303650).sum := by decide
  have hdescent : baseEnd_1303650 < baseStart_1303650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303666 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1303666 : Nat := 118140960795 + 1303666 * 2 ^ 59
def prefixEnd_1303666 : Nat := 4983230072969 + 3 ^ 40 * 1303666 * 2
def baseEnd_1303666 : Nat := 669407270924401634479555

theorem tailTrace_1303666 : CollatzResearch.WordTrace tailWord_1303666 prefixEnd_1303666 669407270924401634479555 := by
  unfold tailWord_1303666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887151323762051317990713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31699070196698803514641901 11887151323762051317990713)
  ·
    refine ⟨8915363492821538488493035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11887151323762051317990713 8915363492821538488493035)
    ·
      refine ⟨13373045239232307732739553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8915363492821538488493035 13373045239232307732739553)
      ·
        refine ⟨10029783929424230799554665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13373045239232307732739553 10029783929424230799554665)
        ·
          refine ⟨7522337947068173099665999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10029783929424230799554665 7522337947068173099665999)
          ·
            refine ⟨11283506920602259649498999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522337947068173099665999 11283506920602259649498999)
            ·
              refine ⟨16925260380903389474248499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11283506920602259649498999 16925260380903389474248499)
              ·
                refine ⟨25387890571355084211372749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16925260380903389474248499 25387890571355084211372749)
                ·
                  refine ⟨9520458964258156579264781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25387890571355084211372749 9520458964258156579264781)
                  ·
                    refine ⟨3570172111596808717224293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9520458964258156579264781 3570172111596808717224293)
                    ·
                      refine ⟨669407270924401634479555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3570172111596808717224293 669407270924401634479555)
                      ·
                        rfl

theorem cell23_1303666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1303666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303666 prefixEnd_1303666 := by exact prefixLift 1303666
  have htrace : WordTrace (prefixWord ++ tailWord_1303666) baseStart_1303666 baseEnd_1303666 := by
    simpa [prefixWord, tailWord_1303666, baseEnd_1303666] using wordTrace_append hprefix tailTrace_1303666
  have hstable : (prefixWord ++ tailWord_1303666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303666).length < 2 ^ (prefixWord ++ tailWord_1303666).sum := by decide
  have hdescent : baseEnd_1303666 < baseStart_1303666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303703 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1303703 : Nat := 118140960795 + 1303703 * 2 ^ 59
def prefixEnd_1303703 : Nat := 4983230072969 + 3 ^ 40 * 1303703 * 2
def baseEnd_1303703 : Nat := 669426269708617989716885

theorem tailTrace_1303703 : CollatzResearch.WordTrace tailWord_1303703 prefixEnd_1303703 669426269708617989716885 := by
  unfold tailWord_1303703
  simp only [CollatzResearch.WordTrace]
  refine ⟨47549954795914160591059763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31699969863942773727373175 47549954795914160591059763)
  ·
    refine ⟨71324932193871240886589645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47549954795914160591059763 71324932193871240886589645)
    ·
      refine ⟨26746849572701715332471117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71324932193871240886589645 26746849572701715332471117)
      ·
        refine ⟨10030068589763143249676669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26746849572701715332471117 10030068589763143249676669)
        ·
          refine ⟨3761275721161178718628751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10030068589763143249676669 3761275721161178718628751)
          ·
            refine ⟨5641913581741768077943127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761275721161178718628751 5641913581741768077943127)
            ·
              refine ⟨8462870372612652116914691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641913581741768077943127 8462870372612652116914691)
              ·
                refine ⟨12694305558918978175372037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462870372612652116914691 12694305558918978175372037)
                ·
                  refine ⟨2380182292297308407882257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12694305558918978175372037 2380182292297308407882257)
                  ·
                    refine ⟨1785136719222981305911693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2380182292297308407882257 1785136719222981305911693)
                    ·
                      refine ⟨669426269708617989716885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1785136719222981305911693 669426269708617989716885)
                      ·
                        rfl

theorem cell23_1303703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1303703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303703 prefixEnd_1303703 := by exact prefixLift 1303703
  have htrace : WordTrace (prefixWord ++ tailWord_1303703) baseStart_1303703 baseEnd_1303703 := by
    simpa [prefixWord, tailWord_1303703, baseEnd_1303703] using wordTrace_append hprefix tailTrace_1303703
  have hstable : (prefixWord ++ tailWord_1303703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303703).length < 2 ^ (prefixWord ++ tailWord_1303703).sum := by decide
  have hdescent : baseEnd_1303703 < baseStart_1303703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303734 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1303734 : Nat := 118140960795 + 1303734 * 2 ^ 59
def prefixEnd_1303734 : Nat := 4983230072969 + 3 ^ 40 * 1303734 * 2
def baseEnd_1303734 : Nat := 669442187608907368429243

theorem tailTrace_1303734 : CollatzResearch.WordTrace tailWord_1303734 prefixEnd_1303734 669442187608907368429243 := by
  unfold tailWord_1303734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971942841175115805339891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31700723639201235256958837 2971942841175115805339891)
  ·
    refine ⟨4457914261762673708009837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2971942841175115805339891 4457914261762673708009837)
    ·
      refine ⟨1671717848161002640503689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4457914261762673708009837 1671717848161002640503689)
      ·
        refine ⟨1253788386120751980377767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1671717848161002640503689 1253788386120751980377767)
        ·
          refine ⟨1880682579181127970566651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253788386120751980377767 1880682579181127970566651)
          ·
            refine ⟨2821023868771691955849977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880682579181127970566651 2821023868771691955849977)
            ·
              refine ⟨2115767901578768966887483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821023868771691955849977 2115767901578768966887483)
              ·
                refine ⟨3173651852368153450331225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115767901578768966887483 3173651852368153450331225)
                ·
                  refine ⟨2380238889276115087748419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3173651852368153450331225 2380238889276115087748419)
                  ·
                    refine ⟨3570358333914172631622629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380238889276115087748419 3570358333914172631622629)
                    ·
                      refine ⟨669442187608907368429243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3570358333914172631622629 669442187608907368429243)
                      ·
                        rfl

theorem cell23_1303734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1303734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303734 prefixEnd_1303734 := by exact prefixLift 1303734
  have htrace : WordTrace (prefixWord ++ tailWord_1303734) baseStart_1303734 baseEnd_1303734 := by
    simpa [prefixWord, tailWord_1303734, baseEnd_1303734] using wordTrace_append hprefix tailTrace_1303734
  have hstable : (prefixWord ++ tailWord_1303734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303734).length < 2 ^ (prefixWord ++ tailWord_1303734).sum := by decide
  have hdescent : baseEnd_1303734 < baseStart_1303734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303743 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 1, 5, 2]
def baseStart_1303743 : Nat := 118140960795 + 1303743 * 2 ^ 59
def prefixEnd_1303743 : Nat := 4983230072969 + 3 ^ 40 * 1303743 * 2
def baseEnd_1303743 : Nat := 669446808934797833216701

theorem tailTrace_1303743 : CollatzResearch.WordTrace tailWord_1303743 prefixEnd_1303743 669446808934797833216701 := by
  unfold tailWord_1303743
  simp only [CollatzResearch.WordTrace]
  refine ⟨47551413715769247422515883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31700942477179498281677255 47551413715769247422515883)
  ·
    refine ⟨71327120573653871133773825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47551413715769247422515883 71327120573653871133773825)
    ·
      refine ⟨53495340430240403350330369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71327120573653871133773825 53495340430240403350330369)
      ·
        refine ⟨40121505322680302512747777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53495340430240403350330369 40121505322680302512747777)
        ·
          refine ⟨30091128992010226884560833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40121505322680302512747777 30091128992010226884560833)
          ·
            refine ⟨22568346744007670163420625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30091128992010226884560833 22568346744007670163420625)
            ·
              refine ⟨16926260058005752622565469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22568346744007670163420625 16926260058005752622565469)
              ·
                refine ⟨6347347521752157233462051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16926260058005752622565469 6347347521752157233462051)
                ·
                  refine ⟨9521021282628235850193077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347347521752157233462051 9521021282628235850193077)
                  ·
                    refine ⟨892595745246397110955601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9521021282628235850193077 892595745246397110955601)
                    ·
                      refine ⟨669446808934797833216701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892595745246397110955601 669446808934797833216701)
                      ·
                        rfl

theorem cell23_1303743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_1303743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303743 prefixEnd_1303743 := by exact prefixLift 1303743
  have htrace : WordTrace (prefixWord ++ tailWord_1303743) baseStart_1303743 baseEnd_1303743 := by
    simpa [prefixWord, tailWord_1303743, baseEnd_1303743] using wordTrace_append hprefix tailTrace_1303743
  have hstable : (prefixWord ++ tailWord_1303743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303743).length < 2 ^ (prefixWord ++ tailWord_1303743).sum := by decide
  have hdescent : baseEnd_1303743 < baseStart_1303743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303794 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1303794 : Nat := 118140960795 + 1303794 * 2 ^ 59
def prefixEnd_1303794 : Nat := 4983230072969 + 3 ^ 40 * 1303794 * 2
def baseEnd_1303794 : Nat := 669472996448177133678967

theorem tailTrace_1303794 : CollatzResearch.WordTrace tailWord_1303794 prefixEnd_1303794 669472996448177133678967 := by
  unfold tailWord_1303794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888318459646120783155609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31702182559056322088414957 11888318459646120783155609)
  ·
    refine ⟨8916238844734590587366707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11888318459646120783155609 8916238844734590587366707)
    ·
      refine ⟨13374358267101885881050061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8916238844734590587366707 13374358267101885881050061)
      ·
        refine ⟨5015384350163207205393773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13374358267101885881050061 5015384350163207205393773)
        ·
          refine ⟨1880769131311202702022665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5015384350163207205393773 1880769131311202702022665)
          ·
            refine ⟨1410576848483402026516999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880769131311202702022665 1410576848483402026516999)
            ·
              refine ⟨2115865272725103039775499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410576848483402026516999 2115865272725103039775499)
              ·
                refine ⟨3173797909087654559663249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115865272725103039775499 3173797909087654559663249)
                ·
                  refine ⟨2380348431815740919747437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3173797909087654559663249 2380348431815740919747437)
                  ·
                    refine ⟨892630661930902844905289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380348431815740919747437 892630661930902844905289)
                    ·
                      refine ⟨669472996448177133678967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892630661930902844905289 669472996448177133678967)
                      ·
                        rfl

theorem cell23_1303794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1303794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303794 prefixEnd_1303794 := by exact prefixLift 1303794
  have htrace : WordTrace (prefixWord ++ tailWord_1303794) baseStart_1303794 baseEnd_1303794 := by
    simpa [prefixWord, tailWord_1303794, baseEnd_1303794] using wordTrace_append hprefix tailTrace_1303794
  have hstable : (prefixWord ++ tailWord_1303794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303794).length < 2 ^ (prefixWord ++ tailWord_1303794).sum := by decide
  have hdescent : baseEnd_1303794 < baseStart_1303794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303804 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_1303804 : Nat := 118140960795 + 1303804 * 2 ^ 59
def prefixEnd_1303804 : Nat := 4983230072969 + 3 ^ 40 * 1303804 * 2
def baseEnd_1303804 : Nat := 223159377084907364851307

theorem tailTrace_1303804 : CollatzResearch.WordTrace tailWord_1303804 prefixEnd_1303804 223159377084907364851307 := by
  unfold tailWord_1303804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23776819284274127420243233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31702425712365503226990977 23776819284274127420243233)
  ·
    refine ⟨17832614463205595565182425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23776819284274127420243233 17832614463205595565182425)
    ·
      refine ⟨13374460847404196673886819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17832614463205595565182425 13374460847404196673886819)
      ·
        refine ⟨20061691271106295010830229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13374460847404196673886819 20061691271106295010830229)
        ·
          refine ⟨940391778333107578632667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20061691271106295010830229 940391778333107578632667)
          ·
            refine ⟨1410587667499661367949001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940391778333107578632667 1410587667499661367949001)
            ·
              refine ⟨1057940750624746025961751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410587667499661367949001 1057940750624746025961751)
              ·
                refine ⟨1586911125937119038942627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057940750624746025961751 1586911125937119038942627)
                ·
                  refine ⟨2380366688905678558413941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586911125937119038942627 2380366688905678558413941)
                  ·
                    refine ⟨223159377084907364851307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2380366688905678558413941 223159377084907364851307)
                    ·
                      rfl

theorem cell23_1303804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_1303804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303804 prefixEnd_1303804 := by exact prefixLift 1303804
  have htrace : WordTrace (prefixWord ++ tailWord_1303804) baseStart_1303804 baseEnd_1303804 := by
    simpa [prefixWord, tailWord_1303804, baseEnd_1303804] using wordTrace_append hprefix tailTrace_1303804
  have hstable : (prefixWord ++ tailWord_1303804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303804).length < 2 ^ (prefixWord ++ tailWord_1303804).sum := by decide
  have hdescent : baseEnd_1303804 < baseStart_1303804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303807 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 1, 1, 4]
def baseStart_1303807 : Nat := 118140960795 + 1303807 * 2 ^ 59
def prefixEnd_1303807 : Nat := 4983230072969 + 3 ^ 40 * 1303807 * 2
def baseEnd_1303807 : Nat := 669479671696685582816407

theorem tailTrace_1303807 : CollatzResearch.WordTrace tailWord_1303807 prefixEnd_1303807 669479671696685582816407 := by
  unfold tailWord_1303807
  simp only [CollatzResearch.WordTrace]
  refine ⟨47553747987537386352845675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31702498658358257568563783 47553747987537386352845675)
  ·
    refine ⟨71330621981306079529268513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47553747987537386352845675 71330621981306079529268513)
    ·
      refine ⟨53497966485979559646951385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71330621981306079529268513 53497966485979559646951385)
      ·
        refine ⟨40123474864484669735213539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53497966485979559646951385 40123474864484669735213539)
        ·
          refine ⟨60185212296727004602820309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40123474864484669735213539 60185212296727004602820309)
          ·
            refine ⟨1410590913204539170378601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60185212296727004602820309 1410590913204539170378601)
            ·
              refine ⟨1057943184903404377783951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410590913204539170378601 1057943184903404377783951)
              ·
                refine ⟨1586914777355106566675927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057943184903404377783951 1586914777355106566675927)
                ·
                  refine ⟨2380372166032659850013891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586914777355106566675927 2380372166032659850013891)
                  ·
                    refine ⟨3570558249048989775020837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380372166032659850013891 3570558249048989775020837)
                    ·
                      refine ⟨669479671696685582816407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3570558249048989775020837 669479671696685582816407)
                      ·
                        rfl

theorem cell23_1303807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_1303807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303807 prefixEnd_1303807 := by exact prefixLift 1303807
  have htrace : WordTrace (prefixWord ++ tailWord_1303807) baseStart_1303807 baseEnd_1303807 := by
    simpa [prefixWord, tailWord_1303807, baseEnd_1303807] using wordTrace_append hprefix tailTrace_1303807
  have hstable : (prefixWord ++ tailWord_1303807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303807).length < 2 ^ (prefixWord ++ tailWord_1303807).sum := by decide
  have hdescent : baseEnd_1303807 < baseStart_1303807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303837 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1303837 : Nat := 118140960795 + 1303837 * 2 ^ 59
def prefixEnd_1303837 : Nat := 4983230072969 + 3 ^ 40 * 1303837 * 2
def baseEnd_1303837 : Nat := 669495076116320465441269

theorem tailTrace_1303837 : CollatzResearch.WordTrace tailWord_1303837 prefixEnd_1303837 669495076116320465441269 := by
  unfold tailWord_1303837
  simp only [CollatzResearch.WordTrace]
  refine ⟨47554842177428701476437765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31703228118285800984291843 47554842177428701476437765)
  ·
    refine ⟨8916532908267881526832081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47554842177428701476437765 8916532908267881526832081)
    ·
      refine ⟨6687399681200911145124061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8916532908267881526832081 6687399681200911145124061)
      ·
        refine ⟨2507774880450341679421523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6687399681200911145124061 2507774880450341679421523)
        ·
          refine ⟨3761662320675512519132285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507774880450341679421523 3761662320675512519132285)
          ·
            refine ⟨1410623370253317194674607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3761662320675512519132285 1410623370253317194674607)
            ·
              refine ⟨2115935055379975792011911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410623370253317194674607 2115935055379975792011911)
              ·
                refine ⟨3173902583069963688017867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115935055379975792011911 3173902583069963688017867)
                ·
                  refine ⟨4760853874604945532026801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173902583069963688017867 4760853874604945532026801)
                  ·
                    refine ⟨3570640405953709149020101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4760853874604945532026801 3570640405953709149020101)
                    ·
                      refine ⟨669495076116320465441269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3570640405953709149020101 669495076116320465441269)
                      ·
                        rfl

theorem cell23_1303837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1303837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303837 prefixEnd_1303837 := by exact prefixLift 1303837
  have htrace : WordTrace (prefixWord ++ tailWord_1303837) baseStart_1303837 baseEnd_1303837 := by
    simpa [prefixWord, tailWord_1303837, baseEnd_1303837] using wordTrace_append hprefix tailTrace_1303837
  have hstable : (prefixWord ++ tailWord_1303837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303837).length < 2 ^ (prefixWord ++ tailWord_1303837).sum := by decide
  have hdescent : baseEnd_1303837 < baseStart_1303837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303913 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_1303913 : Nat := 118140960795 + 1303913 * 2 ^ 59
def prefixEnd_1303913 : Nat := 4983230072969 + 3 ^ 40 * 1303913 * 2
def baseEnd_1303913 : Nat := 669534100646062168090919

theorem tailTrace_1303913 : CollatzResearch.WordTrace tailWord_1303913 prefixEnd_1303913 669534100646062168090919 := by
  unfold tailWord_1303913
  simp only [CollatzResearch.WordTrace]
  refine ⟨47557614125153366456204393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31705076083435577637469595 47557614125153366456204393)
  ·
    refine ⟨35668210593865024842153295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47557614125153366456204393 35668210593865024842153295)
    ·
      refine ⟨53502315890797537263229943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35668210593865024842153295 53502315890797537263229943)
      ·
        refine ⟨80253473836196305894844915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53502315890797537263229943 80253473836196305894844915)
        ·
          refine ⟨120380210754294458842267373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80253473836196305894844915 120380210754294458842267373)
          ·
            refine ⟨45142579032860422065850265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120380210754294458842267373 45142579032860422065850265)
            ·
              refine ⟨33856934274645316549387699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45142579032860422065850265 33856934274645316549387699)
              ·
                refine ⟨50785401411967974824081549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33856934274645316549387699 50785401411967974824081549)
                ·
                  refine ⟨19044525529487990559030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50785401411967974824081549 19044525529487990559030581)
                  ·
                    refine ⟨1785424268389499114909117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19044525529487990559030581 1785424268389499114909117)
                    ·
                      refine ⟨669534100646062168090919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1785424268389499114909117 669534100646062168090919)
                      ·
                        rfl

theorem cell23_1303913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_1303913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303913 prefixEnd_1303913 := by exact prefixLift 1303913
  have htrace : WordTrace (prefixWord ++ tailWord_1303913) baseStart_1303913 baseEnd_1303913 := by
    simpa [prefixWord, tailWord_1303913, baseEnd_1303913] using wordTrace_append hprefix tailTrace_1303913
  have hstable : (prefixWord ++ tailWord_1303913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303913).length < 2 ^ (prefixWord ++ tailWord_1303913).sum := by decide
  have hdescent : baseEnd_1303913 < baseStart_1303913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303914 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1303914 : Nat := 118140960795 + 1303914 * 2 ^ 59
def prefixEnd_1303914 : Nat := 4983230072969 + 3 ^ 40 * 1303914 * 2
def baseEnd_1303914 : Nat := 669534614126716664178415

theorem tailTrace_1303914 : CollatzResearch.WordTrace tailWord_1303914 prefixEnd_1303914 669534614126716664178415 := by
  unfold tailWord_1303914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11889412649537435906747699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31705100398766495751327197 11889412649537435906747699)
  ·
    refine ⟨17834118974306153860121549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11889412649537435906747699 17834118974306153860121549)
    ·
      refine ⟨6687794615364807697545581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17834118974306153860121549 6687794615364807697545581)
      ·
        refine ⟨2507922980761802886579593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6687794615364807697545581 2507922980761802886579593)
        ·
          refine ⟨1880942235571352164934695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507922980761802886579593 1880942235571352164934695)
          ·
            refine ⟨2821413353357028247402043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880942235571352164934695 2821413353357028247402043)
            ·
              refine ⟨4232120030035542371103065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821413353357028247402043 4232120030035542371103065)
              ·
                refine ⟨3174090022526656778327299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4232120030035542371103065 3174090022526656778327299)
                ·
                  refine ⟨4761135033789985167490949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174090022526656778327299 4761135033789985167490949)
                  ·
                    refine ⟨892712818835622218904553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4761135033789985167490949 892712818835622218904553)
                    ·
                      refine ⟨669534614126716664178415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892712818835622218904553 669534614126716664178415)
                      ·
                        rfl

theorem cell23_1303914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1303914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303914 prefixEnd_1303914 := by exact prefixLift 1303914
  have htrace : WordTrace (prefixWord ++ tailWord_1303914) baseStart_1303914 baseEnd_1303914 := by
    simpa [prefixWord, tailWord_1303914, baseEnd_1303914] using wordTrace_append hprefix tailTrace_1303914
  have hstable : (prefixWord ++ tailWord_1303914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303914).length < 2 ^ (prefixWord ++ tailWord_1303914).sum := by decide
  have hdescent : baseEnd_1303914 < baseStart_1303914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303918 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1303918 : Nat := 118140960795 + 1303918 * 2 ^ 59
def prefixEnd_1303918 : Nat := 4983230072969 + 3 ^ 40 * 1303918 * 2
def baseEnd_1303918 : Nat := 669536668049334648528397

theorem tailTrace_1303918 : CollatzResearch.WordTrace tailWord_1303918 prefixEnd_1303918 669536668049334648528397 := by
  unfold tailWord_1303918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944724561266906538767051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31705197660090168206757605 5944724561266906538767051)
  ·
    refine ⟨8917086841900359808150577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5944724561266906538767051 8917086841900359808150577)
    ·
      refine ⟨6687815131425269856112933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8917086841900359808150577 6687815131425269856112933)
      ·
        refine ⟨1253965337142238098021175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6687815131425269856112933 1253965337142238098021175)
        ·
          refine ⟨1880948005713357147031763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253965337142238098021175 1880948005713357147031763)
          ·
            refine ⟨2821422008570035720547645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880948005713357147031763 2821422008570035720547645)
            ·
              refine ⟨1058033253213763395205367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2821422008570035720547645 1058033253213763395205367)
              ·
                refine ⟨1587049879820645092808051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058033253213763395205367 1587049879820645092808051)
                ·
                  refine ⟨2380574819730967639212077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587049879820645092808051 2380574819730967639212077)
                  ·
                    refine ⟨892715557399112864704529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380574819730967639212077 892715557399112864704529)
                    ·
                      refine ⟨669536668049334648528397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892715557399112864704529 669536668049334648528397)
                      ·
                        rfl

theorem cell23_1303918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1303918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303918 prefixEnd_1303918 := by exact prefixLift 1303918
  have htrace : WordTrace (prefixWord ++ tailWord_1303918) baseStart_1303918 baseEnd_1303918 := by
    simpa [prefixWord, tailWord_1303918, baseEnd_1303918] using wordTrace_append hprefix tailTrace_1303918
  have hstable : (prefixWord ++ tailWord_1303918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303918).length < 2 ^ (prefixWord ++ tailWord_1303918).sum := by decide
  have hdescent : baseEnd_1303918 < baseStart_1303918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303920 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 5]
def baseStart_1303920 : Nat := 118140960795 + 1303920 * 2 ^ 59
def prefixEnd_1303920 : Nat := 4983230072969 + 3 ^ 40 * 1303920 * 2
def baseEnd_1303920 : Nat := 74393077223404848967043

theorem tailTrace_1303920 : CollatzResearch.WordTrace tailWord_1303920 prefixEnd_1303920 74393077223404848967043 := by
  unfold tailWord_1303920
  simp only [CollatzResearch.WordTrace]
  refine ⟨23778934718064003325854607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31705246290752004434472809 23778934718064003325854607)
  ·
    refine ⟨35668402077096004988781911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23778934718064003325854607 35668402077096004988781911)
    ·
      refine ⟨53502603115644007483172867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35668402077096004988781911 53502603115644007483172867)
      ·
        refine ⟨80253904673466011224759301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53502603115644007483172867 80253904673466011224759301)
        ·
          refine ⟨15047607126274877104642369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80253904673466011224759301 15047607126274877104642369)
          ·
            refine ⟨11285705344706157828481777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15047607126274877104642369 11285705344706157828481777)
            ·
              refine ⟨8464279008529618371361333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11285705344706157828481777 8464279008529618371361333)
              ·
                refine ⟨793526157049651722315125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8464279008529618371361333 793526157049651722315125)
                ·
                  refine ⟨74393077223404848967043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793526157049651722315125 74393077223404848967043)
                  ·
                    rfl

theorem cell23_1303920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 5].length) (baseStart_1303920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303920 prefixEnd_1303920 := by exact prefixLift 1303920
  have htrace : WordTrace (prefixWord ++ tailWord_1303920) baseStart_1303920 baseEnd_1303920 := by
    simpa [prefixWord, tailWord_1303920, baseEnd_1303920] using wordTrace_append hprefix tailTrace_1303920
  have hstable : (prefixWord ++ tailWord_1303920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303920).length < 2 ^ (prefixWord ++ tailWord_1303920).sum := by decide
  have hdescent : baseEnd_1303920 < baseStart_1303920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303953 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_1303953 : Nat := 118140960795 + 1303953 * 2 ^ 59
def prefixEnd_1303953 : Nat := 4983230072969 + 3 ^ 40 * 1303953 * 2
def baseEnd_1303953 : Nat := 669554639872242011590735

theorem tailTrace_1303953 : CollatzResearch.WordTrace tailWord_1303953 prefixEnd_1303953 669554639872242011590735 := by
  unfold tailWord_1303953
  simp only [CollatzResearch.WordTrace]
  refine ⟨47559073045008453287660513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31706048696672302191773675 47559073045008453287660513)
  ·
    refine ⟨35669304783756339965745385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47559073045008453287660513 35669304783756339965745385)
    ·
      refine ⟨26751978587817254974309039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35669304783756339965745385 26751978587817254974309039)
      ·
        refine ⟨40127967881725882461463559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26751978587817254974309039 40127967881725882461463559)
        ·
          refine ⟨60191951822588823692195339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40127967881725882461463559 60191951822588823692195339)
          ·
            refine ⟨90287927733883235538293009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60191951822588823692195339 90287927733883235538293009)
            ·
              refine ⟨67715945800412426653719757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90287927733883235538293009 67715945800412426653719757)
              ·
                refine ⟨25393479675154659995144909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67715945800412426653719757 25393479675154659995144909)
                ·
                  refine ⟨9522554878182997498179341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25393479675154659995144909 9522554878182997498179341)
                  ·
                    refine ⟨3570958079318624061817253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9522554878182997498179341 3570958079318624061817253)
                    ·
                      refine ⟨669554639872242011590735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3570958079318624061817253 669554639872242011590735)
                      ·
                        rfl

theorem cell23_1303953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_1303953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303953 prefixEnd_1303953 := by exact prefixLift 1303953
  have htrace : WordTrace (prefixWord ++ tailWord_1303953) baseStart_1303953 baseEnd_1303953 := by
    simpa [prefixWord, tailWord_1303953, baseEnd_1303953] using wordTrace_append hprefix tailTrace_1303953
  have hstable : (prefixWord ++ tailWord_1303953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303953).length < 2 ^ (prefixWord ++ tailWord_1303953).sum := by decide
  have hdescent : baseEnd_1303953 < baseStart_1303953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303967 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 2, 5]
def baseStart_1303967 : Nat := 118140960795 + 1303967 * 2 ^ 59
def prefixEnd_1303967 : Nat := 4983230072969 + 3 ^ 40 * 1303967 * 2
def baseEnd_1303967 : Nat := 223187276200468318938557

theorem tailTrace_1303967 : CollatzResearch.WordTrace tailWord_1303967 prefixEnd_1303967 223187276200468318938557 := by
  unfold tailWord_1303967
  simp only [CollatzResearch.WordTrace]
  refine ⟨47559583666957733678670155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31706389111305155785780103 47559583666957733678670155)
  ·
    refine ⟨71339375500436600518005233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47559583666957733678670155 71339375500436600518005233)
    ·
      refine ⟨53504531625327450388503925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71339375500436600518005233 53504531625327450388503925)
      ·
        refine ⟨5016049839874448473922243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53504531625327450388503925 5016049839874448473922243)
        ·
          refine ⟨7524074759811672710883365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016049839874448473922243 7524074759811672710883365)
          ·
            refine ⟨1410764017464688633290631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7524074759811672710883365 1410764017464688633290631)
            ·
              refine ⟨2116146026197032949935947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410764017464688633290631 2116146026197032949935947)
              ·
                refine ⟨3174219039295549424903921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116146026197032949935947 3174219039295549424903921)
                ·
                  refine ⟨2380664279471662068677941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174219039295549424903921 2380664279471662068677941)
                  ·
                    refine ⟨223187276200468318938557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2380664279471662068677941 223187276200468318938557)
                    ·
                      rfl

theorem cell23_1303967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_1303967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303967 prefixEnd_1303967 := by exact prefixLift 1303967
  have htrace : WordTrace (prefixWord ++ tailWord_1303967) baseStart_1303967 baseEnd_1303967 := by
    simpa [prefixWord, tailWord_1303967, baseEnd_1303967] using wordTrace_append hprefix tailTrace_1303967
  have hstable : (prefixWord ++ tailWord_1303967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303967).length < 2 ^ (prefixWord ++ tailWord_1303967).sum := by decide
  have hdescent : baseEnd_1303967 < baseStart_1303967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303973 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_1303973 : Nat := 118140960795 + 1303973 * 2 ^ 59
def prefixEnd_1303973 : Nat := 4983230072969 + 3 ^ 40 * 1303973 * 2
def baseEnd_1303973 : Nat := 669564909485331933340643

theorem tailTrace_1303973 : CollatzResearch.WordTrace tailWord_1303973 prefixEnd_1303973 669564909485331933340643 := by
  unfold tailWord_1303973
  simp only [CollatzResearch.WordTrace]
  refine ⟨47559802504935996703388573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31706535003290664468925715 47559802504935996703388573)
  ·
    refine ⟨17834925939350998763770715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47559802504935996703388573 17834925939350998763770715)
    ·
      refine ⟨26752388909026498145656073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17834925939350998763770715 26752388909026498145656073)
      ·
        refine ⟨20064291681769873609242055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26752388909026498145656073 20064291681769873609242055)
        ·
          refine ⟨30096437522654810413863083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20064291681769873609242055 30096437522654810413863083)
          ·
            refine ⟨45144656283982215620794625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30096437522654810413863083 45144656283982215620794625)
            ·
              refine ⟨33858492212986661715595969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45144656283982215620794625 33858492212986661715595969)
              ·
                refine ⟨25393869159739996286696977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33858492212986661715595969 25393869159739996286696977)
                ·
                  refine ⟨19045401869804997215022733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25393869159739996286696977 19045401869804997215022733)
                  ·
                    refine ⟨7142025701176873955633525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19045401869804997215022733 7142025701176873955633525)
                    ·
                      refine ⟨669564909485331933340643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7142025701176873955633525 669564909485331933340643)
                      ·
                        rfl

theorem cell23_1303973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_1303973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303973 prefixEnd_1303973 := by exact prefixLift 1303973
  have htrace : WordTrace (prefixWord ++ tailWord_1303973) baseStart_1303973 baseEnd_1303973 := by
    simpa [prefixWord, tailWord_1303973, baseEnd_1303973] using wordTrace_append hprefix tailTrace_1303973
  have hstable : (prefixWord ++ tailWord_1303973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303973).length < 2 ^ (prefixWord ++ tailWord_1303973).sum := by decide
  have hdescent : baseEnd_1303973 < baseStart_1303973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303983 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_1303983 : Nat := 118140960795 + 1303983 * 2 ^ 59
def prefixEnd_1303983 : Nat := 4983230072969 + 3 ^ 40 * 1303983 * 2
def baseEnd_1303983 : Nat := 669570044291876894215597

theorem tailTrace_1303983 : CollatzResearch.WordTrace tailWord_1303983 prefixEnd_1303983 669570044291876894215597 := by
  unfold tailWord_1303983
  simp only [CollatzResearch.WordTrace]
  refine ⟨47560167234899768411252603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31706778156599845607501735 47560167234899768411252603)
  ·
    refine ⟨71340250852349652616878905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47560167234899768411252603 71340250852349652616878905)
    ·
      refine ⟨53505188139262239462659179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71340250852349652616878905 53505188139262239462659179)
      ·
        refine ⟨80257782208893359193988769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53505188139262239462659179 80257782208893359193988769)
        ·
          refine ⟨60193336656670019395491577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80257782208893359193988769 60193336656670019395491577)
          ·
            refine ⟨45145002492502514546618683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60193336656670019395491577 45145002492502514546618683)
            ·
              refine ⟨67717503738753771819928025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45145002492502514546618683 67717503738753771819928025)
              ·
                refine ⟨50788127804065328864946019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67717503738753771819928025 50788127804065328864946019)
                ·
                  refine ⟨76182191706097993297419029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50788127804065328864946019 76182191706097993297419029)
                  ·
                    refine ⟨3571040236223343435816517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76182191706097993297419029 3571040236223343435816517)
                    ·
                      refine ⟨669570044291876894215597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3571040236223343435816517 669570044291876894215597)
                      ·
                        rfl

theorem cell23_1303983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_1303983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303983 prefixEnd_1303983 := by exact prefixLift 1303983
  have htrace : WordTrace (prefixWord ++ tailWord_1303983) baseStart_1303983 baseEnd_1303983 := by
    simpa [prefixWord, tailWord_1303983, baseEnd_1303983] using wordTrace_append hprefix tailTrace_1303983
  have hstable : (prefixWord ++ tailWord_1303983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303983).length < 2 ^ (prefixWord ++ tailWord_1303983).sum := by decide
  have hdescent : baseEnd_1303983 < baseStart_1303983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303997 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1303997 : Nat := 118140960795 + 1303997 * 2 ^ 59
def prefixEnd_1303997 : Nat := 4983230072969 + 3 ^ 40 * 1303997 * 2
def baseEnd_1303997 : Nat := 223192411007013279813511

theorem tailTrace_1303997 : CollatzResearch.WordTrace tailWord_1303997 prefixEnd_1303997 223192411007013279813511 := by
  unfold tailWord_1303997
  simp only [CollatzResearch.WordTrace]
  refine ⟨47560677856849048802262245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31707118571232699201508163 47560677856849048802262245)
  ·
    refine ⟨8917627098159196650424171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47560677856849048802262245 8917627098159196650424171)
    ·
      refine ⟨13376440647238794975636257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917627098159196650424171 13376440647238794975636257)
      ·
        refine ⟨10032330485429096231727193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13376440647238794975636257 10032330485429096231727193)
        ·
          refine ⟨7524247864071822173795395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10032330485429096231727193 7524247864071822173795395)
          ·
            refine ⟨11286371796107733260693093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524247864071822173795395 11286371796107733260693093)
            ·
              refine ⟨2116194711770199986379955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11286371796107733260693093 2116194711770199986379955)
              ·
                refine ⟨3174292067655299979569933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116194711770199986379955 3174292067655299979569933)
                ·
                  refine ⟨1190359525370737492338725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3174292067655299979569933 1190359525370737492338725)
                  ·
                    refine ⟨223192411007013279813511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1190359525370737492338725 223192411007013279813511)
                    ·
                      rfl

theorem cell23_1303997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1303997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1303997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1303997 prefixEnd_1303997 := by exact prefixLift 1303997
  have htrace : WordTrace (prefixWord ++ tailWord_1303997) baseStart_1303997 baseEnd_1303997 := by
    simpa [prefixWord, tailWord_1303997, baseEnd_1303997] using wordTrace_append hprefix tailTrace_1303997
  have hstable : (prefixWord ++ tailWord_1303997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303997).length < 2 ^ (prefixWord ++ tailWord_1303997).sum := by decide
  have hdescent : baseEnd_1303997 < baseStart_1303997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304004 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1304004 : Nat := 118140960795 + 1304004 * 2 ^ 59
def prefixEnd_1304004 : Nat := 4983230072969 + 3 ^ 40 * 1304004 * 2
def baseEnd_1304004 : Nat := 669580827385621312053001

theorem tailTrace_1304004 : CollatzResearch.WordTrace tailWord_1304004 prefixEnd_1304004 669580827385621312053001 := by
  unfold tailWord_1304004
  simp only [CollatzResearch.WordTrace]
  refine ⟨23780466583911844498883533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31707288778549125998511377 23780466583911844498883533)
  ·
    refine ⟨8917674968966941687081325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23780466583911844498883533 8917674968966941687081325)
    ·
      refine ⟨3344128113362603132655497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8917674968966941687081325 3344128113362603132655497)
      ·
        refine ⟨2508096085021952349491623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3344128113362603132655497 2508096085021952349491623)
        ·
          refine ⟨3762144127532928524237435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508096085021952349491623 3762144127532928524237435)
          ·
            refine ⟨5643216191299392786356153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762144127532928524237435 5643216191299392786356153)
            ·
              refine ⟨4232412143474544589767115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5643216191299392786356153 4232412143474544589767115)
              ·
                refine ⟨6348618215211816884650673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232412143474544589767115 6348618215211816884650673)
                ·
                  refine ⟨4761463661408862663488005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348618215211816884650673 4761463661408862663488005)
                  ·
                    refine ⟨892774436514161749404001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4761463661408862663488005 892774436514161749404001)
                    ·
                      refine ⟨669580827385621312053001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892774436514161749404001 669580827385621312053001)
                      ·
                        rfl

theorem cell23_1304004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1304004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304004 prefixEnd_1304004 := by exact prefixLift 1304004
  have htrace : WordTrace (prefixWord ++ tailWord_1304004) baseStart_1304004 baseEnd_1304004 := by
    simpa [prefixWord, tailWord_1304004, baseEnd_1304004] using wordTrace_append hprefix tailTrace_1304004
  have hstable : (prefixWord ++ tailWord_1304004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304004).length < 2 ^ (prefixWord ++ tailWord_1304004).sum := by decide
  have hdescent : baseEnd_1304004 < baseStart_1304004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304023 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 9]
def baseStart_1304023 : Nat := 118140960795 + 1304023 * 2 ^ 59
def prefixEnd_1304023 : Nat := 4983230072969 + 3 ^ 40 * 1304023 * 2
def baseEnd_1304023 : Nat := 223196861172685579238471

theorem tailTrace_1304023 : CollatzResearch.WordTrace tailWord_1304023 prefixEnd_1304023 223196861172685579238471 := by
  unfold tailWord_1304023
  simp only [CollatzResearch.WordTrace]
  refine ⟨47561626154754855242708723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31707750769836570161805815 47561626154754855242708723)
  ·
    refine ⟨71342439232132282864063085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47561626154754855242708723 71342439232132282864063085)
    ·
      refine ⟨26753414712049606074023657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71342439232132282864063085 26753414712049606074023657)
      ·
        refine ⟨20065061034037204555517743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26753414712049606074023657 20065061034037204555517743)
        ·
          refine ⟨30097591551055806833276615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20065061034037204555517743 30097591551055806833276615)
          ·
            refine ⟨45146387326583710249914923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30097591551055806833276615 45146387326583710249914923)
            ·
              refine ⟨67719580989875565374872385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45146387326583710249914923 67719580989875565374872385)
              ·
                refine ⟨50789685742406674031154289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67719580989875565374872385 50789685742406674031154289)
                ·
                  refine ⟨38092264306805005523365717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50789685742406674031154289 38092264306805005523365717)
                  ·
                    refine ⟨223196861172685579238471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38092264306805005523365717 223196861172685579238471)
                    ·
                      rfl

theorem cell23_1304023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_1304023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304023 prefixEnd_1304023 := by exact prefixLift 1304023
  have htrace : WordTrace (prefixWord ++ tailWord_1304023) baseStart_1304023 baseEnd_1304023 := by
    simpa [prefixWord, tailWord_1304023, baseEnd_1304023] using wordTrace_append hprefix tailTrace_1304023
  have hstable : (prefixWord ++ tailWord_1304023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304023).length < 2 ^ (prefixWord ++ tailWord_1304023).sum := by decide
  have hdescent : baseEnd_1304023 < baseStart_1304023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304047 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 4, 3, 2]
def baseStart_1304047 : Nat := 118140960795 + 1304047 * 2 ^ 59
def prefixEnd_1304047 : Nat := 4983230072969 + 3 ^ 40 * 1304047 * 2
def baseEnd_1304047 : Nat := 669602907053764643815303

theorem tailTrace_1304047 : CollatzResearch.WordTrace tailWord_1304047 prefixEnd_1304047 669602907053764643815303 := by
  unfold tailWord_1304047
  simp only [CollatzResearch.WordTrace]
  refine ⟨47562501506667907341582395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31708334337778604894388263 47562501506667907341582395)
  ·
    refine ⟨71343752260001861012373593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47562501506667907341582395 71343752260001861012373593)
    ·
      refine ⟨53507814195001395759280195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71343752260001861012373593 53507814195001395759280195)
      ·
        refine ⟨80261721292502093638920293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53507814195001395759280195 80261721292502093638920293)
        ·
          refine ⟨15049072742344142557297555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80261721292502093638920293 15049072742344142557297555)
          ·
            refine ⟨22573609113516213835946333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15049072742344142557297555 22573609113516213835946333)
            ·
              refine ⟨8465103417568580188479875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22573609113516213835946333 8465103417568580188479875)
              ·
                refine ⟨12697655126352870282719813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8465103417568580188479875 12697655126352870282719813)
                ·
                  refine ⟨2380810336191163178009965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12697655126352870282719813 2380810336191163178009965)
                  ·
                    refine ⟨892803876071686191753737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380810336191163178009965 892803876071686191753737)
                    ·
                      refine ⟨669602907053764643815303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892803876071686191753737 669602907053764643815303)
                      ·
                        rfl

theorem cell23_1304047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 3, 2].length) (baseStart_1304047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304047 prefixEnd_1304047 := by exact prefixLift 1304047
  have htrace : WordTrace (prefixWord ++ tailWord_1304047) baseStart_1304047 baseEnd_1304047 := by
    simpa [prefixWord, tailWord_1304047, baseEnd_1304047] using wordTrace_append hprefix tailTrace_1304047
  have hstable : (prefixWord ++ tailWord_1304047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304047).length < 2 ^ (prefixWord ++ tailWord_1304047).sum := by decide
  have hdescent : baseEnd_1304047 < baseStart_1304047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304074 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_1304074 : Nat := 118140960795 + 1304074 * 2 ^ 59
def prefixEnd_1304074 : Nat := 4983230072969 + 3 ^ 40 * 1304074 * 2
def baseEnd_1304074 : Nat := 223205590343812012725893

theorem tailTrace_1304074 : CollatzResearch.WordTrace tailWord_1304074 prefixEnd_1304074 223205590343812012725893 := by
  unfold tailWord_1304074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11890871569392522738203819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31708990851713393968543517 11890871569392522738203819)
  ·
    refine ⟨17836307354088784107305729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11890871569392522738203819 17836307354088784107305729)
    ·
      refine ⟨13377230515566588080479297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17836307354088784107305729 13377230515566588080479297)
      ·
        refine ⟨10032922886674941060359473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13377230515566588080479297 10032922886674941060359473)
        ·
          refine ⟨7524692165006205795269605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10032922886674941060359473 7524692165006205795269605)
          ·
            refine ⟨1410879780938663586613051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7524692165006205795269605 1410879780938663586613051)
            ·
              refine ⟨2116319671407995379919577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410879780938663586613051 2116319671407995379919577)
              ·
                refine ⟨1587239753555996534939683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116319671407995379919577 1587239753555996534939683)
                ·
                  refine ⟨2380859630333994802409525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587239753555996534939683 2380859630333994802409525)
                  ·
                    refine ⟨223205590343812012725893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2380859630333994802409525 223205590343812012725893)
                    ·
                      rfl

theorem cell23_1304074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_1304074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304074 prefixEnd_1304074 := by exact prefixLift 1304074
  have htrace : WordTrace (prefixWord ++ tailWord_1304074) baseStart_1304074 baseEnd_1304074 := by
    simpa [prefixWord, tailWord_1304074, baseEnd_1304074] using wordTrace_append hprefix tailTrace_1304074
  have hstable : (prefixWord ++ tailWord_1304074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304074).length < 2 ^ (prefixWord ++ tailWord_1304074).sum := by decide
  have hdescent : baseEnd_1304074 < baseStart_1304074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304097 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1304097 : Nat := 118140960795 + 1304097 * 2 ^ 59
def prefixEnd_1304097 : Nat := 4983230072969 + 3 ^ 40 * 1304097 * 2
def baseEnd_1304097 : Nat := 669628581086489448190073

theorem tailTrace_1304097 : CollatzResearch.WordTrace tailWord_1304097 prefixEnd_1304097 669628581086489448190073 := by
  unfold tailWord_1304097
  simp only [CollatzResearch.WordTrace]
  refine ⟨47564325156486765880902545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31709550104324510587268363 47564325156486765880902545)
  ·
    refine ⟨35673243867365074410676909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47564325156486765880902545 35673243867365074410676909)
    ·
      refine ⟨13377466450261902904003841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35673243867365074410676909 13377466450261902904003841)
      ·
        refine ⟨10033099837696427178002881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13377466450261902904003841 10033099837696427178002881)
        ·
          refine ⟨7524824878272320383502161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10033099837696427178002881 7524824878272320383502161)
          ·
            refine ⟨5643618658704240287626621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7524824878272320383502161 5643618658704240287626621)
            ·
              refine ⟨2116356997014090107859983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5643618658704240287626621 2116356997014090107859983)
              ·
                refine ⟨3174535495521135161789975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116356997014090107859983 3174535495521135161789975)
                ·
                  refine ⟨4761803243281702742684963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174535495521135161789975 4761803243281702742684963)
                  ·
                    refine ⟨7142704864922554114027445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761803243281702742684963 7142704864922554114027445)
                    ·
                      refine ⟨669628581086489448190073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7142704864922554114027445 669628581086489448190073)
                      ·
                        rfl

theorem cell23_1304097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1304097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304097 prefixEnd_1304097 := by exact prefixLift 1304097
  have htrace : WordTrace (prefixWord ++ tailWord_1304097) baseStart_1304097 baseEnd_1304097 := by
    simpa [prefixWord, tailWord_1304097, baseEnd_1304097] using wordTrace_append hprefix tailTrace_1304097
  have hstable : (prefixWord ++ tailWord_1304097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304097).length < 2 ^ (prefixWord ++ tailWord_1304097).sum := by decide
  have hdescent : baseEnd_1304097 < baseStart_1304097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304117 : List Nat := [1, 3, 3, 1, 1, 5, 1, 8]
def baseStart_1304117 : Nat := 118140960795 + 1304117 * 2 ^ 59
def prefixEnd_1304117 : Nat := 4983230072969 + 3 ^ 40 * 1304117 * 2
def baseEnd_1304117 : Nat := 24801438914799235923703

theorem tailTrace_1304117 : CollatzResearch.WordTrace tailWord_1304117 prefixEnd_1304117 24801438914799235923703 := by
  unfold tailWord_1304117
  simp only [CollatzResearch.WordTrace]
  refine ⟨47565054616414309296630605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31710036410942872864420403 47565054616414309296630605)
  ·
    refine ⟨17836895481155365986236477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47565054616414309296630605 17836895481155365986236477)
    ·
      refine ⟨6688835805433262244838679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17836895481155365986236477 6688835805433262244838679)
      ·
        refine ⟨10033253708149893367258019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6688835805433262244838679 10033253708149893367258019)
        ·
          refine ⟨15049880562224840050887029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10033253708149893367258019 15049880562224840050887029)
          ·
            refine ⟨1410926302708578754770659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15049880562224840050887029 1410926302708578754770659)
            ·
              refine ⟨2116389454062868132155989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410926302708578754770659 2116389454062868132155989)
              ·
                refine ⟨24801438914799235923703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2116389454062868132155989 24801438914799235923703)
                ·
                  rfl

theorem cell23_1304117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 8].length) (baseStart_1304117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304117 prefixEnd_1304117 := by exact prefixLift 1304117
  have htrace : WordTrace (prefixWord ++ tailWord_1304117) baseStart_1304117 baseEnd_1304117 := by
    simpa [prefixWord, tailWord_1304117, baseEnd_1304117] using wordTrace_append hprefix tailTrace_1304117
  have hstable : (prefixWord ++ tailWord_1304117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304117).length < 2 ^ (prefixWord ++ tailWord_1304117).sum := by decide
  have hdescent : baseEnd_1304117 < baseStart_1304117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304124 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_1304124 : Nat := 118140960795 + 1304124 * 2 ^ 59
def prefixEnd_1304124 : Nat := 4983230072969 + 3 ^ 40 * 1304124 * 2
def baseEnd_1304124 : Nat := 669642445064160842552449

theorem tailTrace_1304124 : CollatzResearch.WordTrace tailWord_1304124 prefixEnd_1304124 669642445064160842552449 := by
  unfold tailWord_1304124
  simp only [CollatzResearch.WordTrace]
  refine ⟨23782654963694474746067713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31710206618259299661423617 23782654963694474746067713)
  ·
    refine ⟨17836991222770856059550785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23782654963694474746067713 17836991222770856059550785)
    ·
      refine ⟨13377743417078142044663089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17836991222770856059550785 13377743417078142044663089)
      ·
        refine ⟨10033307562808606533497317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13377743417078142044663089 10033307562808606533497317)
        ·
          refine ⟨1881245168026613725030747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10033307562808606533497317 1881245168026613725030747)
          ·
            refine ⟨2821867752039920587546121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881245168026613725030747 2821867752039920587546121)
            ·
              refine ⟨2116400814029940440659591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821867752039920587546121 2116400814029940440659591)
              ·
                refine ⟨3174601221044910660989387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116400814029940440659591 3174601221044910660989387)
                ·
                  refine ⟨4761901831567365991484081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174601221044910660989387 4761901831567365991484081)
                  ·
                    refine ⟨3571426373675524493613061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761901831567365991484081 3571426373675524493613061)
                    ·
                      refine ⟨669642445064160842552449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3571426373675524493613061 669642445064160842552449)
                      ·
                        rfl

theorem cell23_1304124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_1304124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304124 prefixEnd_1304124 := by exact prefixLift 1304124
  have htrace : WordTrace (prefixWord ++ tailWord_1304124) baseStart_1304124 baseEnd_1304124 := by
    simpa [prefixWord, tailWord_1304124, baseEnd_1304124] using wordTrace_append hprefix tailTrace_1304124
  have hstable : (prefixWord ++ tailWord_1304124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304124).length < 2 ^ (prefixWord ++ tailWord_1304124).sum := by decide
  have hdescent : baseEnd_1304124 < baseStart_1304124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304127 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_1304127 : Nat := 118140960795 + 1304127 * 2 ^ 59
def prefixEnd_1304127 : Nat := 4983230072969 + 3 ^ 40 * 1304127 * 2
def baseEnd_1304127 : Nat := 669643985506124330814935

theorem tailTrace_1304127 : CollatzResearch.WordTrace tailWord_1304127 prefixEnd_1304127 669643985506124330814935 := by
  unfold tailWord_1304127
  simp only [CollatzResearch.WordTrace]
  refine ⟨47565419346378081004494635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31710279564252054002996423 47565419346378081004494635)
  ·
    refine ⟨71348129019567121506741953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47565419346378081004494635 71348129019567121506741953)
    ·
      refine ⟨53511096764675341130056465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71348129019567121506741953 53511096764675341130056465)
      ·
        refine ⟨40133322573506505847542349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53511096764675341130056465 40133322573506505847542349)
        ·
          refine ⟨15049995965064939692828381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40133322573506505847542349 15049995965064939692828381)
          ·
            refine ⟨5643748486899352384810643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15049995965064939692828381 5643748486899352384810643)
            ·
              refine ⟨8465622730349028577215965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643748486899352384810643 8465622730349028577215965)
              ·
                refine ⟨3174608523880885716455987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8465622730349028577215965 3174608523880885716455987)
                ·
                  refine ⟨4761912785821328574683981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174608523880885716455987 4761912785821328574683981)
                  ·
                    refine ⟨1785717294682998215506493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4761912785821328574683981 1785717294682998215506493)
                    ·
                      refine ⟨669643985506124330814935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1785717294682998215506493 669643985506124330814935)
                      ·
                        rfl

theorem cell23_1304127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_1304127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304127 prefixEnd_1304127 := by exact prefixLift 1304127
  have htrace : WordTrace (prefixWord ++ tailWord_1304127) baseStart_1304127 baseEnd_1304127 := by
    simpa [prefixWord, tailWord_1304127, baseEnd_1304127] using wordTrace_append hprefix tailTrace_1304127
  have hstable : (prefixWord ++ tailWord_1304127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304127).length < 2 ^ (prefixWord ++ tailWord_1304127).sum := by decide
  have hdescent : baseEnd_1304127 < baseStart_1304127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304178 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_1304178 : Nat := 118140960795 + 1304178 * 2 ^ 59
def prefixEnd_1304178 : Nat := 4983230072969 + 3 ^ 40 * 1304178 * 2
def baseEnd_1304178 : Nat := 669670173019503631277201

theorem tailTrace_1304178 : CollatzResearch.WordTrace tailWord_1304178 prefixEnd_1304178 669670173019503631277201 := by
  unfold tailWord_1304178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891819867298329178650297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31711519646128877809734125 11891819867298329178650297)
  ·
    refine ⟨8918864900473746883987723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11891819867298329178650297 8918864900473746883987723)
    ·
      refine ⟨13378297350710620325981585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918864900473746883987723 13378297350710620325981585)
      ·
        refine ⟨10033723013032965244486189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13378297350710620325981585 10033723013032965244486189)
        ·
          refine ⟨3762646129887361966682321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10033723013032965244486189 3762646129887361966682321)
          ·
            refine ⟨2821984597415521475011741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3762646129887361966682321 2821984597415521475011741)
            ·
              refine ⟨1058244224030820553129403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2821984597415521475011741 1058244224030820553129403)
              ·
                refine ⟨1587366336046230829694105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058244224030820553129403 1587366336046230829694105)
                ·
                  refine ⟨1190524752034673122270579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587366336046230829694105 1190524752034673122270579)
                  ·
                    refine ⟨1785787128052009683405869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1190524752034673122270579 1785787128052009683405869)
                    ·
                      refine ⟨669670173019503631277201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1785787128052009683405869 669670173019503631277201)
                      ·
                        rfl

theorem cell23_1304178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_1304178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304178 prefixEnd_1304178 := by exact prefixLift 1304178
  have htrace : WordTrace (prefixWord ++ tailWord_1304178) baseStart_1304178 baseEnd_1304178 := by
    simpa [prefixWord, tailWord_1304178, baseEnd_1304178] using wordTrace_append hprefix tailTrace_1304178
  have hstable : (prefixWord ++ tailWord_1304178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304178).length < 2 ^ (prefixWord ++ tailWord_1304178).sum := by decide
  have hdescent : baseEnd_1304178 < baseStart_1304178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304184 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 8, 2, 2]
def baseStart_1304184 : Nat := 118140960795 + 1304184 * 2 ^ 59
def prefixEnd_1304184 : Nat := 4983230072969 + 3 ^ 40 * 1304184 * 2
def baseEnd_1304184 : Nat := 669673253903430607802173

theorem tailTrace_1304184 : CollatzResearch.WordTrace tailWord_1304184 prefixEnd_1304184 669673253903430607802173 := by
  unfold tailWord_1304184
  simp only [CollatzResearch.WordTrace]
  refine ⟨23783749153585789869659803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31711665538114386492879737 23783749153585789869659803)
  ·
    refine ⟨35675623730378684804489705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23783749153585789869659803 35675623730378684804489705)
    ·
      refine ⟨26756717797784013603367279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35675623730378684804489705 26756717797784013603367279)
      ·
        refine ⟨40135076696676020405050919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26756717797784013603367279 40135076696676020405050919)
        ·
          refine ⟨60202615045014030607576379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40135076696676020405050919 60202615045014030607576379)
          ·
            refine ⟨90303922567521045911364569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60202615045014030607576379 90303922567521045911364569)
            ·
              refine ⟨67727941925640784433523427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90303922567521045911364569 67727941925640784433523427)
              ·
                refine ⟨101591912888461176650285141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67727941925640784433523427 101591912888461176650285141)
                ·
                  refine ⟨1190530229161654413870529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 101591912888461176650285141 1190530229161654413870529)
                  ·
                    refine ⟨892897671871240810402897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1190530229161654413870529 892897671871240810402897)
                    ·
                      refine ⟨669673253903430607802173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 892897671871240810402897 669673253903430607802173)
                      ·
                        rfl

theorem cell23_1304184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_1304184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304184 prefixEnd_1304184 := by exact prefixLift 1304184
  have htrace : WordTrace (prefixWord ++ tailWord_1304184) baseStart_1304184 baseEnd_1304184 := by
    simpa [prefixWord, tailWord_1304184, baseEnd_1304184] using wordTrace_append hprefix tailTrace_1304184
  have hstable : (prefixWord ++ tailWord_1304184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304184).length < 2 ^ (prefixWord ++ tailWord_1304184).sum := by decide
  have hdescent : baseEnd_1304184 < baseStart_1304184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304217 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_1304217 : Nat := 118140960795 + 1304217 * 2 ^ 59
def prefixEnd_1304217 : Nat := 4983230072969 + 3 ^ 40 * 1304217 * 2
def baseEnd_1304217 : Nat := 669690198765028978689521

theorem tailTrace_1304217 : CollatzResearch.WordTrace tailWord_1304217 prefixEnd_1304217 669690198765028978689521 := by
  unfold tailWord_1304217
  simp only [CollatzResearch.WordTrace]
  refine ⟨47568701916052026375270905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31712467944034684250180603 47568701916052026375270905)
  ·
    refine ⟨35676526437039019781453179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47568701916052026375270905 35676526437039019781453179)
    ·
      refine ⟨53514789655558529672179769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35676526437039019781453179 53514789655558529672179769)
      ·
        refine ⟨40136092241668897254134827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53514789655558529672179769 40136092241668897254134827)
        ·
          refine ⟨60204138362503345881202241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40136092241668897254134827 60204138362503345881202241)
          ·
            refine ⟨45153103771877509410901681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60204138362503345881202241 45153103771877509410901681)
            ·
              refine ⟨33864827828908132058176261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45153103771877509410901681 33864827828908132058176261)
              ·
                refine ⟨6349655217920274760908049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33864827828908132058176261 6349655217920274760908049)
                ·
                  refine ⟨4762241413440206070681037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6349655217920274760908049 4762241413440206070681037)
                  ·
                    refine ⟨1785840530040077276505389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4762241413440206070681037 1785840530040077276505389)
                    ·
                      refine ⟨669690198765028978689521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1785840530040077276505389 669690198765028978689521)
                      ·
                        rfl

theorem cell23_1304217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_1304217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304217 prefixEnd_1304217 := by exact prefixLift 1304217
  have htrace : WordTrace (prefixWord ++ tailWord_1304217) baseStart_1304217 baseEnd_1304217 := by
    simpa [prefixWord, tailWord_1304217, baseEnd_1304217] using wordTrace_append hprefix tailTrace_1304217
  have hstable : (prefixWord ++ tailWord_1304217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304217).length < 2 ^ (prefixWord ++ tailWord_1304217).sum := by decide
  have hdescent : baseEnd_1304217 < baseStart_1304217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304224 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 7]
def baseStart_1304224 : Nat := 118140960795 + 1304224 * 2 ^ 59
def prefixEnd_1304224 : Nat := 4983230072969 + 3 ^ 40 * 1304224 * 2
def baseEnd_1304224 : Nat := 74410421458845605700221

theorem tailTrace_1304224 : CollatzResearch.WordTrace tailWord_1304224 prefixEnd_1304224 74410421458845605700221 := by
  unfold tailWord_1304224
  simp only [CollatzResearch.WordTrace]
  refine ⟨23784478613513333285387863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31712638151351111047183817 23784478613513333285387863)
  ·
    refine ⟨35676717920269999928081795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23784478613513333285387863 35676717920269999928081795)
    ·
      refine ⟨53515076880404999892122693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35676717920269999928081795 53515076880404999892122693)
      ·
        refine ⟨10034076915075937479773005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53515076880404999892122693 10034076915075937479773005)
        ·
          refine ⟨3762778843153476554914877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10034076915075937479773005 3762778843153476554914877)
          ·
            refine ⟨1411042066182553708093079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3762778843153476554914877 1411042066182553708093079)
            ·
              refine ⟨2116563099273830562139619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411042066182553708093079 2116563099273830562139619)
              ·
                refine ⟨3174844648910745843209429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116563099273830562139619 3174844648910745843209429)
                ·
                  refine ⟨74410421458845605700221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3174844648910745843209429 74410421458845605700221)
                  ·
                    rfl

theorem cell23_1304224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_1304224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304224 prefixEnd_1304224 := by exact prefixLift 1304224
  have htrace : WordTrace (prefixWord ++ tailWord_1304224) baseStart_1304224 baseEnd_1304224 := by
    simpa [prefixWord, tailWord_1304224, baseEnd_1304224] using wordTrace_append hprefix tailTrace_1304224
  have hstable : (prefixWord ++ tailWord_1304224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304224).length < 2 ^ (prefixWord ++ tailWord_1304224).sum := by decide
  have hdescent : baseEnd_1304224 < baseStart_1304224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304254 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1304254 : Nat := 118140960795 + 1304254 * 2 ^ 59
def prefixEnd_1304254 : Nat := 4983230072969 + 3 ^ 40 * 1304254 * 2
def baseEnd_1304254 : Nat := 223236399183081777975617

theorem tailTrace_1304254 : CollatzResearch.WordTrace tailWord_1304254 prefixEnd_1304254 223236399183081777975617 := by
  unfold tailWord_1304254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5946256427114747711795977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31713367611278654462911877 5946256427114747711795977)
  ·
    refine ⟨4459692320336060783846983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5946256427114747711795977 4459692320336060783846983)
    ·
      refine ⟨6689538480504091175770475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4459692320336060783846983 6689538480504091175770475)
      ·
        refine ⟨10034307720756136763655713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6689538480504091175770475 10034307720756136763655713)
        ·
          refine ⟨7525730790567102572741785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10034307720756136763655713 7525730790567102572741785)
          ·
            refine ⟨5644298092925326929556339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525730790567102572741785 5644298092925326929556339)
            ·
              refine ⟨8466447139387990394334509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644298092925326929556339 8466447139387990394334509)
              ·
                refine ⟨3174917677270496397875441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8466447139387990394334509 3174917677270496397875441)
                ·
                  refine ⟨2381188257952872298406581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174917677270496397875441 2381188257952872298406581)
                  ·
                    refine ⟨223236399183081777975617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2381188257952872298406581 223236399183081777975617)
                    ·
                      rfl

theorem cell23_1304254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1304254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304254 prefixEnd_1304254 := by exact prefixLift 1304254
  have htrace : WordTrace (prefixWord ++ tailWord_1304254) baseStart_1304254 baseEnd_1304254 := by
    simpa [prefixWord, tailWord_1304254, baseEnd_1304254] using wordTrace_append hprefix tailTrace_1304254
  have hstable : (prefixWord ++ tailWord_1304254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304254).length < 2 ^ (prefixWord ++ tailWord_1304254).sum := by decide
  have hdescent : baseEnd_1304254 < baseStart_1304254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304301 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1304301 : Nat := 118140960795 + 1304301 * 2 ^ 59
def prefixEnd_1304301 : Nat := 4983230072969 + 3 ^ 40 * 1304301 * 2
def baseEnd_1304301 : Nat := 223244443713335550013045

theorem tailTrace_1304301 : CollatzResearch.WordTrace tailWord_1304301 prefixEnd_1304301 223244443713335550013045 := by
  unfold tailWord_1304301
  simp only [CollatzResearch.WordTrace]
  refine ⟨47571765647747708721328757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31714510431831805814219171 47571765647747708721328757)
  ·
    refine ⟨4459853029476347692624571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47571765647747708721328757 4459853029476347692624571)
    ·
      refine ⟨6689779544214521538936857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4459853029476347692624571 6689779544214521538936857)
      ·
        refine ⟨5017334658160891154202643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6689779544214521538936857 5017334658160891154202643)
        ·
          refine ⟨7526001987241336731303965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017334658160891154202643 7526001987241336731303965)
          ·
            refine ⟨2822250745215501274238987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7526001987241336731303965 2822250745215501274238987)
            ·
              refine ⟨4233376117823251911358481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822250745215501274238987 4233376117823251911358481)
              ·
                refine ⟨3175032088367438933518861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4233376117823251911358481 3175032088367438933518861)
                ·
                  refine ⟨1190637033137789600069573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3175032088367438933518861 1190637033137789600069573)
                  ·
                    refine ⟨223244443713335550013045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1190637033137789600069573 223244443713335550013045)
                    ·
                      rfl

theorem cell23_1304301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1304301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304301 prefixEnd_1304301 := by exact prefixLift 1304301
  have htrace : WordTrace (prefixWord ++ tailWord_1304301) baseStart_1304301 baseEnd_1304301 := by
    simpa [prefixWord, tailWord_1304301, baseEnd_1304301] using wordTrace_append hprefix tailTrace_1304301
  have hstable : (prefixWord ++ tailWord_1304301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304301).length < 2 ^ (prefixWord ++ tailWord_1304301).sum := by decide
  have hdescent : baseEnd_1304301 < baseStart_1304301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304308 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1304308 : Nat := 118140960795 + 1304308 * 2 ^ 59
def prefixEnd_1304308 : Nat := 4983230072969 + 3 ^ 40 * 1304308 * 2
def baseEnd_1304308 : Nat := 669736925504588122651603

theorem tailTrace_1304308 : CollatzResearch.WordTrace tailWord_1304308 prefixEnd_1304308 669736925504588122651603 := by
  unfold tailWord_1304308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23786010479361174458416789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31714680639148232611222385 23786010479361174458416789)
  ·
    refine ⟨1114969241220055052738287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23786010479361174458416789 1114969241220055052738287)
    ·
      refine ⟨1672453861830082579107431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114969241220055052738287 1672453861830082579107431)
      ·
        refine ⟨2508680792745123868661147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672453861830082579107431 2508680792745123868661147)
        ·
          refine ⟨3763021189117685802991721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508680792745123868661147 3763021189117685802991721)
          ·
            refine ⟨2822265891838264352243791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3763021189117685802991721 2822265891838264352243791)
            ·
              refine ⟨4233398837757396528365687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822265891838264352243791 4233398837757396528365687)
              ·
                refine ⟨6350098256636094792548531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4233398837757396528365687 6350098256636094792548531)
                ·
                  refine ⟨9525147384954142188822797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6350098256636094792548531 9525147384954142188822797)
                  ·
                    refine ⟨3571930269357803320808549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9525147384954142188822797 3571930269357803320808549)
                    ·
                      refine ⟨669736925504588122651603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3571930269357803320808549 669736925504588122651603)
                      ·
                        rfl

theorem cell23_1304308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1304308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304308 prefixEnd_1304308 := by exact prefixLift 1304308
  have htrace : WordTrace (prefixWord ++ tailWord_1304308) baseStart_1304308 baseEnd_1304308 := by
    simpa [prefixWord, tailWord_1304308, baseEnd_1304308] using wordTrace_append hprefix tailTrace_1304308
  have hstable : (prefixWord ++ tailWord_1304308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304308).length < 2 ^ (prefixWord ++ tailWord_1304308).sum := by decide
  have hdescent : baseEnd_1304308 < baseStart_1304308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304341 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_1304341 : Nat := 118140960795 + 1304341 * 2 ^ 59
def prefixEnd_1304341 : Nat := 4983230072969 + 3 ^ 40 * 1304341 * 2
def baseEnd_1304341 : Nat := 669753870366186493538951

theorem tailTrace_1304341 : CollatzResearch.WordTrace tailWord_1304341 prefixEnd_1304341 669753870366186493538951 := by
  unfold tailWord_1304341
  simp only [CollatzResearch.WordTrace]
  refine ⟨47573224567602795552784877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31715483045068530368523251 47573224567602795552784877)
  ·
    refine ⟨17839959212851048332294329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47573224567602795552784877 17839959212851048332294329)
    ·
      refine ⟨13379969409638286249220747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17839959212851048332294329 13379969409638286249220747)
      ·
        refine ⟨20069954114457429373831121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13379969409638286249220747 20069954114457429373831121)
        ·
          refine ⟨15052465585843072030373341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20069954114457429373831121 15052465585843072030373341)
          ·
            refine ⟨5644674594691152011390003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15052465585843072030373341 5644674594691152011390003)
            ·
              refine ⟨8467011892036728017085005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644674594691152011390003 8467011892036728017085005)
              ·
                refine ⟨3175129459513773006406877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8467011892036728017085005 3175129459513773006406877)
                ·
                  refine ⟨1190673547317664877402579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3175129459513773006406877 1190673547317664877402579)
                  ·
                    refine ⟨1786010320976497316103869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1190673547317664877402579 1786010320976497316103869)
                    ·
                      refine ⟨669753870366186493538951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786010320976497316103869 669753870366186493538951)
                      ·
                        rfl

theorem cell23_1304341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_1304341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304341 prefixEnd_1304341 := by exact prefixLift 1304341
  have htrace : WordTrace (prefixWord ++ tailWord_1304341) baseStart_1304341 baseEnd_1304341 := by
    simpa [prefixWord, tailWord_1304341, baseEnd_1304341] using wordTrace_append hprefix tailTrace_1304341
  have hstable : (prefixWord ++ tailWord_1304341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304341).length < 2 ^ (prefixWord ++ tailWord_1304341).sum := by decide
  have hdescent : baseEnd_1304341 < baseStart_1304341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304384 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_1304384 : Nat := 118140960795 + 1304384 * 2 ^ 59
def prefixEnd_1304384 : Nat := 4983230072969 + 3 ^ 40 * 1304384 * 2
def baseEnd_1304384 : Nat := 669775950034329825301253

theorem tailTrace_1304384 : CollatzResearch.WordTrace tailWord_1304384 prefixEnd_1304384 669775950034329825301253 := by
  unfold tailWord_1304384
  simp only [CollatzResearch.WordTrace]
  refine ⟨23787396453223506948300103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31716528604298009264400137 23787396453223506948300103)
  ·
    refine ⟨35681094679835260422450155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23787396453223506948300103 35681094679835260422450155)
    ·
      refine ⟨53521642019752890633675233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35681094679835260422450155 53521642019752890633675233)
      ·
        refine ⟨40141231514814667975256425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53521642019752890633675233 40141231514814667975256425)
        ·
          refine ⟨30105923636111000981442319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40141231514814667975256425 30105923636111000981442319)
          ·
            refine ⟨45158885454166501472163479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30105923636111000981442319 45158885454166501472163479)
            ·
              refine ⟨67738328181249752208245219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45158885454166501472163479 67738328181249752208245219)
              ·
                refine ⟨101607492271874628312367829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67738328181249752208245219 101607492271874628312367829)
                ·
                  refine ⟨2381425600122061601071121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101607492271874628312367829 2381425600122061601071121)
                  ·
                    refine ⟨1786069200091546200803341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2381425600122061601071121 1786069200091546200803341)
                    ·
                      refine ⟨669775950034329825301253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786069200091546200803341 669775950034329825301253)
                      ·
                        rfl

theorem cell23_1304384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_1304384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304384 prefixEnd_1304384 := by exact prefixLift 1304384
  have htrace : WordTrace (prefixWord ++ tailWord_1304384) baseStart_1304384 baseEnd_1304384 := by
    simpa [prefixWord, tailWord_1304384, baseEnd_1304384] using wordTrace_append hprefix tailTrace_1304384
  have hstable : (prefixWord ++ tailWord_1304384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304384).length < 2 ^ (prefixWord ++ tailWord_1304384).sum := by decide
  have hdescent : baseEnd_1304384 < baseStart_1304384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304387 : List Nat := [1, 1, 1, 3, 1, 5, 11]
def baseStart_1304387 : Nat := 118140960795 + 1304387 * 2 ^ 59
def prefixEnd_1304387 : Nat := 4983230072969 + 3 ^ 40 * 1304387 * 2
def baseEnd_1304387 : Nat := 8268857907114732266219

theorem tailTrace_1304387 : CollatzResearch.WordTrace tailWord_1304387 prefixEnd_1304387 8268857907114732266219 := by
  unfold tailWord_1304387
  simp only [CollatzResearch.WordTrace]
  refine ⟨47574902325436145408959415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31716601550290763605972943 47574902325436145408959415)
  ·
    refine ⟨71362353488154218113439123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47574902325436145408959415 71362353488154218113439123)
    ·
      refine ⟨107043530232231327170158685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71362353488154218113439123 107043530232231327170158685)
      ·
        refine ⟨40141323837086747688809507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107043530232231327170158685 40141323837086747688809507)
        ·
          refine ⟨60211985755630121533214261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40141323837086747688809507 60211985755630121533214261)
          ·
            refine ⟨5644873664590323893738837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60211985755630121533214261 5644873664590323893738837)
            ·
              refine ⟨8268857907114732266219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5644873664590323893738837 8268857907114732266219)
              ·
                rfl

theorem cell23_1304387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 11].length) (baseStart_1304387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304387 prefixEnd_1304387 := by exact prefixLift 1304387
  have htrace : WordTrace (prefixWord ++ tailWord_1304387) baseStart_1304387 baseEnd_1304387 := by
    simpa [prefixWord, tailWord_1304387, baseEnd_1304387] using wordTrace_append hprefix tailTrace_1304387
  have hstable : (prefixWord ++ tailWord_1304387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304387).length < 2 ^ (prefixWord ++ tailWord_1304387).sum := by decide
  have hdescent : baseEnd_1304387 < baseStart_1304387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304404 : List Nat := [2, 4, 1, 1, 3, 1, 1, 10]
def baseStart_1304404 : Nat := 118140960795 + 1304404 * 2 ^ 59
def prefixEnd_1304404 : Nat := 4983230072969 + 3 ^ 40 * 1304404 * 2
def baseEnd_1304404 : Nat := 24806897023978509150043

theorem tailTrace_1304404 : CollatzResearch.WordTrace tailWord_1304404 prefixEnd_1304404 24806897023978509150043 := by
  unfold tailWord_1304404
  simp only [CollatzResearch.WordTrace]
  refine ⟨23787761183187278656164133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31717014910916371541552177 23787761183187278656164133)
  ·
    refine ⟨4460205221847614748030775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23787761183187278656164133 4460205221847614748030775)
    ·
      refine ⟨6690307832771422122046163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4460205221847614748030775 6690307832771422122046163)
      ·
        refine ⟨10035461749157133183069245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6690307832771422122046163 10035461749157133183069245)
        ·
          refine ⟨3763298155933924943650967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10035461749157133183069245 3763298155933924943650967)
          ·
            refine ⟨5644947233900887415476451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763298155933924943650967 5644947233900887415476451)
            ·
              refine ⟨8467420850851331123214677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644947233900887415476451 8467420850851331123214677)
              ·
                refine ⟨24806897023978509150043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8467420850851331123214677 24806897023978509150043)
                ·
                  rfl

theorem cell23_1304404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 10].length) (baseStart_1304404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304404 prefixEnd_1304404 := by exact prefixLift 1304404
  have htrace : WordTrace (prefixWord ++ tailWord_1304404) baseStart_1304404 baseEnd_1304404 := by
    simpa [prefixWord, tailWord_1304404, baseEnd_1304404] using wordTrace_append hprefix tailTrace_1304404
  have hstable : (prefixWord ++ tailWord_1304404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304404).length < 2 ^ (prefixWord ++ tailWord_1304404).sum := by decide
  have hdescent : baseEnd_1304404 < baseStart_1304404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304418 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1304418 : Nat := 118140960795 + 1304418 * 2 ^ 59
def prefixEnd_1304418 : Nat := 4983230072969 + 3 ^ 40 * 1304418 * 2
def baseEnd_1304418 : Nat := 669793408376582692276097

theorem tailTrace_1304418 : CollatzResearch.WordTrace tailWord_1304418 prefixEnd_1304418 669793408376582692276097 := by
  unfold tailWord_1304418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894008247080959425834477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31717355325549225135558605 11894008247080959425834477)
  ·
    refine ⟨4460253092655359784687929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11894008247080959425834477 4460253092655359784687929)
    ·
      refine ⟨3345189819491519838515947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4460253092655359784687929 3345189819491519838515947)
      ·
        refine ⟨5017784729237279757773921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345189819491519838515947 5017784729237279757773921)
        ·
          refine ⟨3763338546927959818330441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5017784729237279757773921 3763338546927959818330441)
          ·
            refine ⟨2822503910195969863747831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3763338546927959818330441 2822503910195969863747831)
            ·
              refine ⟨4233755865293954795621747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822503910195969863747831 4233755865293954795621747)
              ·
                refine ⟨6350633797940932193432621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4233755865293954795621747 6350633797940932193432621)
                ·
                  refine ⟨2381487674227849572537233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6350633797940932193432621 2381487674227849572537233)
                  ·
                    refine ⟨1786115755670887179402925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2381487674227849572537233 1786115755670887179402925)
                    ·
                      refine ⟨669793408376582692276097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786115755670887179402925 669793408376582692276097)
                      ·
                        rfl

theorem cell23_1304418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1304418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304418 prefixEnd_1304418 := by exact prefixLift 1304418
  have htrace : WordTrace (prefixWord ++ tailWord_1304418) baseStart_1304418 baseEnd_1304418 := by
    simpa [prefixWord, tailWord_1304418, baseEnd_1304418] using wordTrace_append hprefix tailTrace_1304418
  have hstable : (prefixWord ++ tailWord_1304418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304418).length < 2 ^ (prefixWord ++ tailWord_1304418).sum := by decide
  have hdescent : baseEnd_1304418 < baseStart_1304418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304448 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 2, 1, 3]
def baseStart_1304448 : Nat := 118140960795 + 1304448 * 2 ^ 59
def prefixEnd_1304448 : Nat := 4983230072969 + 3 ^ 40 * 1304448 * 2
def baseEnd_1304448 : Nat := 669808812796217574900959

theorem tailTrace_1304448 : CollatzResearch.WordTrace tailWord_1304448 prefixEnd_1304448 669808812796217574900959 := by
  unfold tailWord_1304448
  simp only [CollatzResearch.WordTrace]
  refine ⟨23788563589107576413464999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31718084785476768551286665 23788563589107576413464999)
  ·
    refine ⟨35682845383661364620197499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23788563589107576413464999 35682845383661364620197499)
    ·
      refine ⟨53524268075492046930296249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35682845383661364620197499 53524268075492046930296249)
      ·
        refine ⟨40143201056619035197722187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53524268075492046930296249 40143201056619035197722187)
        ·
          refine ⟨60214801584928552796583281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40143201056619035197722187 60214801584928552796583281)
          ·
            refine ⟨45161101188696414597437461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60214801584928552796583281 45161101188696414597437461)
            ·
              refine ⟨2116926618220144434254881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45161101188696414597437461 2116926618220144434254881)
              ·
                refine ⟨1587694963665108325691161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116926618220144434254881 1587694963665108325691161)
                ·
                  refine ⟨1190771222748831244268371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587694963665108325691161 1190771222748831244268371)
                  ·
                    refine ⟨1786156834123246866402557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1190771222748831244268371 1786156834123246866402557)
                    ·
                      refine ⟨669808812796217574900959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786156834123246866402557 669808812796217574900959)
                      ·
                        rfl

theorem cell23_1304448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_1304448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304448 prefixEnd_1304448 := by exact prefixLift 1304448
  have htrace : WordTrace (prefixWord ++ tailWord_1304448) baseStart_1304448 baseEnd_1304448 := by
    simpa [prefixWord, tailWord_1304448, baseEnd_1304448] using wordTrace_append hprefix tailTrace_1304448
  have hstable : (prefixWord ++ tailWord_1304448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304448).length < 2 ^ (prefixWord ++ tailWord_1304448).sum := by decide
  have hdescent : baseEnd_1304448 < baseStart_1304448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304449 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1304449 : Nat := 118140960795 + 1304449 * 2 ^ 59
def prefixEnd_1304449 : Nat := 4983230072969 + 3 ^ 40 * 1304449 * 2
def baseEnd_1304449 : Nat := 669809326276872070988455

theorem tailTrace_1304449 : CollatzResearch.WordTrace tailWord_1304449 prefixEnd_1304449 669809326276872070988455 := by
  unfold tailWord_1304449
  simp only [CollatzResearch.WordTrace]
  refine ⟨47577163651211529997716401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31718109100807686665144267 47577163651211529997716401)
  ·
    refine ⟨35682872738408647498287301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47577163651211529997716401 35682872738408647498287301)
    ·
      refine ⟨6690538638451621405928869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35682872738408647498287301 6690538638451621405928869)
      ·
        refine ⟨1254475994709679013611663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6690538638451621405928869 1254475994709679013611663)
        ·
          refine ⟨1881713992064518520417495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254475994709679013611663 1881713992064518520417495)
          ·
            refine ⟨2822570988096777780626243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881713992064518520417495 2822570988096777780626243)
            ·
              refine ⟨4233856482145166670939365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822570988096777780626243 4233856482145166670939365)
              ·
                refine ⟨793848090402218750801131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4233856482145166670939365 793848090402218750801131)
                ·
                  refine ⟨1190772135603328126201697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793848090402218750801131 1190772135603328126201697)
                  ·
                    refine ⟨893079101702496094651273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1190772135603328126201697 893079101702496094651273)
                    ·
                      refine ⟨669809326276872070988455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 893079101702496094651273 669809326276872070988455)
                      ·
                        rfl

theorem cell23_1304449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1304449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304449 prefixEnd_1304449 := by exact prefixLift 1304449
  have htrace : WordTrace (prefixWord ++ tailWord_1304449) baseStart_1304449 baseEnd_1304449 := by
    simpa [prefixWord, tailWord_1304449, baseEnd_1304449] using wordTrace_append hprefix tailTrace_1304449
  have hstable : (prefixWord ++ tailWord_1304449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304449).length < 2 ^ (prefixWord ++ tailWord_1304449).sum := by decide
  have hdescent : baseEnd_1304449 < baseStart_1304449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304501 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1304501 : Nat := 118140960795 + 1304501 * 2 ^ 59
def prefixEnd_1304501 : Nat := 4983230072969 + 3 ^ 40 * 1304501 * 2
def baseEnd_1304501 : Nat := 669836027270905867538215

theorem tailTrace_1304501 : CollatzResearch.WordTrace tailWord_1304501 prefixEnd_1304501 669836027270905867538215 := by
  unfold tailWord_1304501
  simp only [CollatzResearch.WordTrace]
  refine ⟨47579060247023142878609357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31719373498015428585739571 47579060247023142878609357)
  ·
    refine ⟨17842147592633678579478509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47579060247023142878609357 17842147592633678579478509)
    ·
      refine ⟨6690805347237629467304441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17842147592633678579478509 6690805347237629467304441)
      ·
        refine ⟨5018104010428222100478331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6690805347237629467304441 5018104010428222100478331)
        ·
          refine ⟨7527156015642333150717497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5018104010428222100478331 7527156015642333150717497)
          ·
            refine ⟨5645367011731749863038123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7527156015642333150717497 5645367011731749863038123)
            ·
              refine ⟨8468050517597624794557185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645367011731749863038123 8468050517597624794557185)
              ·
                refine ⟨6351037888198218595917889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8468050517597624794557185 6351037888198218595917889)
                ·
                  refine ⟨4763278416148663946938417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6351037888198218595917889 4763278416148663946938417)
                  ·
                    refine ⟨3572458812111497960203813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763278416148663946938417 3572458812111497960203813)
                    ·
                      refine ⟨669836027270905867538215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3572458812111497960203813 669836027270905867538215)
                      ·
                        rfl

theorem cell23_1304501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1304501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304501 prefixEnd_1304501 := by exact prefixLift 1304501
  have htrace : WordTrace (prefixWord ++ tailWord_1304501) baseStart_1304501 baseEnd_1304501 := by
    simpa [prefixWord, tailWord_1304501, baseEnd_1304501] using wordTrace_append hprefix tailTrace_1304501
  have hstable : (prefixWord ++ tailWord_1304501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304501).length < 2 ^ (prefixWord ++ tailWord_1304501).sum := by decide
  have hdescent : baseEnd_1304501 < baseStart_1304501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304511 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 5]
def baseStart_1304511 : Nat := 118140960795 + 1304511 * 2 ^ 59
def prefixEnd_1304511 : Nat := 4983230072969 + 3 ^ 40 * 1304511 * 2
def baseEnd_1304511 : Nat := 74426795786383425379241

theorem tailTrace_1304511 : CollatzResearch.WordTrace tailWord_1304511 prefixEnd_1304511 74426795786383425379241 := by
  unfold tailWord_1304511
  simp only [CollatzResearch.WordTrace]
  refine ⟨47579424976986914586473387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31719616651324609724315591 47579424976986914586473387)
  ·
    refine ⟨71369137465480371879710081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47579424976986914586473387 71369137465480371879710081)
    ·
      refine ⟨53526853099110278909782561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71369137465480371879710081 53526853099110278909782561)
      ·
        refine ⟨40145139824332709182336921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53526853099110278909782561 40145139824332709182336921)
        ·
          refine ⟨30108854868249531886752691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40145139824332709182336921 30108854868249531886752691)
          ·
            refine ⟨45163282302374297830129037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30108854868249531886752691 45163282302374297830129037)
            ·
              refine ⟨16936230863390361686298389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45163282302374297830129037 16936230863390361686298389)
              ·
                refine ⟨793885821721423204045237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16936230863390361686298389 793885821721423204045237)
                ·
                  refine ⟨74426795786383425379241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793885821721423204045237 74426795786383425379241)
                  ·
                    rfl

theorem cell23_1304511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 5].length) (baseStart_1304511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304511 prefixEnd_1304511 := by exact prefixLift 1304511
  have htrace : WordTrace (prefixWord ++ tailWord_1304511) baseStart_1304511 baseEnd_1304511 := by
    simpa [prefixWord, tailWord_1304511, baseEnd_1304511] using wordTrace_append hprefix tailTrace_1304511
  have hstable : (prefixWord ++ tailWord_1304511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304511).length < 2 ^ (prefixWord ++ tailWord_1304511).sum := by decide
  have hdescent : baseEnd_1304511 < baseStart_1304511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304558 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1304558 : Nat := 118140960795 + 1304558 * 2 ^ 59
def prefixEnd_1304558 : Nat := 4983230072969 + 3 ^ 40 * 1304558 * 2
def baseEnd_1304558 : Nat := 223288431889404048175151

theorem tailTrace_1304558 : CollatzResearch.WordTrace tailWord_1304558 prefixEnd_1304558 223288431889404048175151 := by
  unfold tailWord_1304558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947642400977080201679291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31720759471877761075622885 5947642400977080201679291)
  ·
    refine ⟨8921463601465620302518937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5947642400977080201679291 8921463601465620302518937)
    ·
      refine ⟨6691097701099215226889203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8921463601465620302518937 6691097701099215226889203)
      ·
        refine ⟨10036646551648822840333805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691097701099215226889203 10036646551648822840333805)
        ·
          refine ⟨3763742456868308565125177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10036646551648822840333805 3763742456868308565125177)
          ·
            refine ⟨2822806842651231423843883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3763742456868308565125177 2822806842651231423843883)
            ·
              refine ⟨4234210263976847135765825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822806842651231423843883 4234210263976847135765825)
              ·
                refine ⟨3175657697982635351824369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4234210263976847135765825 3175657697982635351824369)
                ·
                  refine ⟨2381743273486976513868277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3175657697982635351824369 2381743273486976513868277)
                  ·
                    refine ⟨223288431889404048175151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2381743273486976513868277 223288431889404048175151)
                    ·
                      rfl

theorem cell23_1304558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1304558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304558 prefixEnd_1304558 := by exact prefixLift 1304558
  have htrace : WordTrace (prefixWord ++ tailWord_1304558) baseStart_1304558 baseEnd_1304558 := by
    simpa [prefixWord, tailWord_1304558, baseEnd_1304558] using wordTrace_append hprefix tailTrace_1304558
  have hstable : (prefixWord ++ tailWord_1304558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304558).length < 2 ^ (prefixWord ++ tailWord_1304558).sum := by decide
  have hdescent : baseEnd_1304558 < baseStart_1304558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304618 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_1304618 : Nat := 118140960795 + 1304618 * 2 ^ 59
def prefixEnd_1304618 : Nat := 4983230072969 + 3 ^ 40 * 1304618 * 2
def baseEnd_1304618 : Nat := 74432900500831323308353

theorem tailTrace_1304618 : CollatzResearch.WordTrace tailWord_1304618 prefixEnd_1304618 74432900500831323308353 := by
  unfold tailWord_1304618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11895831896899817965154627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31722218391732847907079005 11895831896899817965154627)
  ·
    refine ⟨17843747845349726947731941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11895831896899817965154627 17843747845349726947731941)
    ·
      refine ⟨3345702721003073802699739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17843747845349726947731941 3345702721003073802699739)
      ·
        refine ⟨5018554081504610704049609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345702721003073802699739 5018554081504610704049609)
        ·
          refine ⟨3763915561128458028037207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5018554081504610704049609 3763915561128458028037207)
          ·
            refine ⟨5645873341692687042055811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763915561128458028037207 5645873341692687042055811)
            ·
              refine ⟨8468810012539030563083717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645873341692687042055811 8468810012539030563083717)
              ·
                refine ⟨1587901877351068230578197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8468810012539030563083717 1587901877351068230578197)
                ·
                  refine ⟨74432900500831323308353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1587901877351068230578197 74432900500831323308353)
                  ·
                    rfl

theorem cell23_1304618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_1304618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304618 prefixEnd_1304618 := by exact prefixLift 1304618
  have htrace : WordTrace (prefixWord ++ tailWord_1304618) baseStart_1304618 baseEnd_1304618 := by
    simpa [prefixWord, tailWord_1304618, baseEnd_1304618] using wordTrace_append hprefix tailTrace_1304618
  have hstable : (prefixWord ++ tailWord_1304618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304618).length < 2 ^ (prefixWord ++ tailWord_1304618).sum := by decide
  have hdescent : baseEnd_1304618 < baseStart_1304618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304622 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1304622 : Nat := 118140960795 + 1304622 * 2 ^ 59
def prefixEnd_1304622 : Nat := 4983230072969 + 3 ^ 40 * 1304622 * 2
def baseEnd_1304622 : Nat := 223299386143366631375053

theorem tailTrace_1304622 : CollatzResearch.WordTrace tailWord_1304622 prefixEnd_1304622 223299386143366631375053 := by
  unfold tailWord_1304622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947934184948097567970515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31722315653056520362509413 5947934184948097567970515)
  ·
    refine ⟨8921901277422146351955773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5947934184948097567970515 8921901277422146351955773)
    ·
      refine ⟨3345712979033304881983415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8921901277422146351955773 3345712979033304881983415)
      ·
        refine ⟨5018569468549957322975123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345712979033304881983415 5018569468549957322975123)
        ·
          refine ⟨7527854202824935984462685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5018569468549957322975123 7527854202824935984462685)
          ·
            refine ⟨2822945326059350994173507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7527854202824935984462685 2822945326059350994173507)
            ·
              refine ⟨4234417989089026491260261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822945326059350994173507 4234417989089026491260261)
              ·
                refine ⟨793953372954192467111299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4234417989089026491260261 793953372954192467111299)
                ·
                  refine ⟨1190930059431288700666949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793953372954192467111299 1190930059431288700666949)
                  ·
                    refine ⟨223299386143366631375053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1190930059431288700666949 223299386143366631375053)
                    ·
                      rfl

theorem cell23_1304622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1304622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304622 prefixEnd_1304622 := by exact prefixLift 1304622
  have htrace : WordTrace (prefixWord ++ tailWord_1304622) baseStart_1304622 baseEnd_1304622 := by
    simpa [prefixWord, tailWord_1304622, baseEnd_1304622] using wordTrace_append hprefix tailTrace_1304622
  have hstable : (prefixWord ++ tailWord_1304622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304622).length < 2 ^ (prefixWord ++ tailWord_1304622).sum := by decide
  have hdescent : baseEnd_1304622 < baseStart_1304622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304631 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 3, 5]
def baseStart_1304631 : Nat := 118140960795 + 1304631 * 2 ^ 59
def prefixEnd_1304631 : Nat := 4983230072969 + 3 ^ 40 * 1304631 * 2
def baseEnd_1304631 : Nat := 223300926585330119637539

theorem tailTrace_1304631 : CollatzResearch.WordTrace tailWord_1304631 prefixEnd_1304631 223300926585330119637539 := by
  unfold tailWord_1304631
  simp only [CollatzResearch.WordTrace]
  refine ⟨47583801736552175080841747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31722534491034783387227831 47583801736552175080841747)
  ·
    refine ⟨71375702604828262621262621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47583801736552175080841747 71375702604828262621262621)
    ·
      refine ⟨26765888476810598482973483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71375702604828262621262621 26765888476810598482973483)
      ·
        refine ⟨40148832715215897724460225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26765888476810598482973483 40148832715215897724460225)
        ·
          refine ⟨30111624536411923293345169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40148832715215897724460225 30111624536411923293345169)
          ·
            refine ⟨22583718402308942470008877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30111624536411923293345169 22583718402308942470008877)
            ·
              refine ⟨8468894400865853426253329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22583718402308942470008877 8468894400865853426253329)
              ·
                refine ⟨6351670800649390069689997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8468894400865853426253329 6351670800649390069689997)
                ·
                  refine ⟨2381876550243521276133749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6351670800649390069689997 2381876550243521276133749)
                  ·
                    refine ⟨223300926585330119637539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2381876550243521276133749 223300926585330119637539)
                    ·
                      rfl

theorem cell23_1304631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_1304631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304631 prefixEnd_1304631 := by exact prefixLift 1304631
  have htrace : WordTrace (prefixWord ++ tailWord_1304631) baseStart_1304631 baseEnd_1304631 := by
    simpa [prefixWord, tailWord_1304631, baseEnd_1304631] using wordTrace_append hprefix tailTrace_1304631
  have hstable : (prefixWord ++ tailWord_1304631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304631).length < 2 ^ (prefixWord ++ tailWord_1304631).sum := by decide
  have hdescent : baseEnd_1304631 < baseStart_1304631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304681 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_1304681 : Nat := 118140960795 + 1304681 * 2 ^ 59
def prefixEnd_1304681 : Nat := 4983230072969 + 3 ^ 40 * 1304681 * 2
def baseEnd_1304681 : Nat := 669928453788715163287387

theorem tailTrace_1304681 : CollatzResearch.WordTrace tailWord_1304681 prefixEnd_1304681 669928453788715163287387 := by
  unfold tailWord_1304681
  simp only [CollatzResearch.WordTrace]
  refine ⟨47585625386371033620161897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31723750257580689080107931 47585625386371033620161897)
  ·
    refine ⟨35689219039778275215121423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47585625386371033620161897 35689219039778275215121423)
    ·
      refine ⟨53533828559667412822682135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35689219039778275215121423 53533828559667412822682135)
      ·
        refine ⟨80300742839501119234023203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53533828559667412822682135 80300742839501119234023203)
        ·
          refine ⟨120451114259251678851034805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80300742839501119234023203 120451114259251678851034805)
          ·
            refine ⟨11292291961804844892284513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120451114259251678851034805 11292291961804844892284513)
            ·
              refine ⟨8469218971353633669213385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11292291961804844892284513 8469218971353633669213385)
              ·
                refine ⟨6351914228515225251910039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8469218971353633669213385 6351914228515225251910039)
                ·
                  refine ⟨9527871342772837877865059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351914228515225251910039 9527871342772837877865059)
                  ·
                    refine ⟨14291807014159256816797589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9527871342772837877865059 14291807014159256816797589)
                    ·
                      refine ⟨669928453788715163287387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14291807014159256816797589 669928453788715163287387)
                      ·
                        rfl

theorem cell23_1304681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_1304681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304681 prefixEnd_1304681 := by exact prefixLift 1304681
  have htrace : WordTrace (prefixWord ++ tailWord_1304681) baseStart_1304681 baseEnd_1304681 := by
    simpa [prefixWord, tailWord_1304681, baseEnd_1304681] using wordTrace_append hprefix tailTrace_1304681
  have hstable : (prefixWord ++ tailWord_1304681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304681).length < 2 ^ (prefixWord ++ tailWord_1304681).sum := by decide
  have hdescent : baseEnd_1304681 < baseStart_1304681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304688 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_1304688 : Nat := 118140960795 + 1304688 * 2 ^ 59
def prefixEnd_1304688 : Nat := 4983230072969 + 3 ^ 40 * 1304688 * 2
def baseEnd_1304688 : Nat := 669932048153296635899855

theorem tailTrace_1304688 : CollatzResearch.WordTrace tailWord_1304688 prefixEnd_1304688 669932048153296635899855 := by
  unfold tailWord_1304688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792940348672836907833359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31723920464897115877111145 23792940348672836907833359)
  ·
    refine ⟨35689410523009255361750039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23792940348672836907833359 35689410523009255361750039)
    ·
      refine ⟨53534115784513883042625059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35689410523009255361750039 53534115784513883042625059)
      ·
        refine ⟨80301173676770824563937589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53534115784513883042625059 80301173676770824563937589)
        ·
          refine ⟨7528235032197264802869149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80301173676770824563937589 7528235032197264802869149)
          ·
            refine ⟨2823088137073974301075931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7528235032197264802869149 2823088137073974301075931)
            ·
              refine ⟨4234632205610961451613897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823088137073974301075931 4234632205610961451613897)
              ·
                refine ⟨3175974154208221088710423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4234632205610961451613897 3175974154208221088710423)
                ·
                  refine ⟨4763961231312331633065635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175974154208221088710423 4763961231312331633065635)
                  ·
                    refine ⟨7145941846968497449598453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4763961231312331633065635 7145941846968497449598453)
                    ·
                      refine ⟨669932048153296635899855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7145941846968497449598453 669932048153296635899855)
                      ·
                        rfl

theorem cell23_1304688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_1304688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304688 prefixEnd_1304688 := by exact prefixLift 1304688
  have htrace : WordTrace (prefixWord ++ tailWord_1304688) baseStart_1304688 baseEnd_1304688 := by
    simpa [prefixWord, tailWord_1304688, baseEnd_1304688] using wordTrace_append hprefix tailTrace_1304688
  have hstable : (prefixWord ++ tailWord_1304688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304688).length < 2 ^ (prefixWord ++ tailWord_1304688).sum := by decide
  have hdescent : baseEnd_1304688 < baseStart_1304688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304731 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_1304731 : Nat := 118140960795 + 1304731 * 2 ^ 59
def prefixEnd_1304731 : Nat := 4983230072969 + 3 ^ 40 * 1304731 * 2
def baseEnd_1304731 : Nat := 669954127821439967662157

theorem tailTrace_1304731 : CollatzResearch.WordTrace tailWord_1304731 prefixEnd_1304731 669954127821439967662157 := by
  unfold tailWord_1304731
  simp only [CollatzResearch.WordTrace]
  refine ⟨47587449036189892159482047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31724966024126594772988031 47587449036189892159482047)
  ·
    refine ⟨71381173554284838239223071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47587449036189892159482047 71381173554284838239223071)
    ·
      refine ⟨107071760331427257358834607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71381173554284838239223071 107071760331427257358834607)
      ·
        refine ⟨160607640497140886038251911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107071760331427257358834607 160607640497140886038251911)
        ·
          refine ⟨240911460745711329057377867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160607640497140886038251911 240911460745711329057377867)
          ·
            refine ⟨361367191118566993586066801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240911460745711329057377867 361367191118566993586066801)
            ·
              refine ⟨271025393338925245189550101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361367191118566993586066801 271025393338925245189550101)
              ·
                refine ⟨12704315312762120868260161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271025393338925245189550101 12704315312762120868260161)
                ·
                  refine ⟨9528236484571590651195121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12704315312762120868260161 9528236484571590651195121)
                  ·
                    refine ⟨7146177363428692988396341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9528236484571590651195121 7146177363428692988396341)
                    ·
                      refine ⟨669954127821439967662157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7146177363428692988396341 669954127821439967662157)
                      ·
                        rfl

theorem cell23_1304731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_1304731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304731 prefixEnd_1304731 := by exact prefixLift 1304731
  have htrace : WordTrace (prefixWord ++ tailWord_1304731) baseStart_1304731 baseEnd_1304731 := by
    simpa [prefixWord, tailWord_1304731, baseEnd_1304731] using wordTrace_append hprefix tailTrace_1304731
  have hstable : (prefixWord ++ tailWord_1304731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304731).length < 2 ^ (prefixWord ++ tailWord_1304731).sum := by decide
  have hdescent : baseEnd_1304731 < baseStart_1304731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304736 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 1, 2, 2]
def baseStart_1304736 : Nat := 118140960795 + 1304736 * 2 ^ 59
def prefixEnd_1304736 : Nat := 4983230072969 + 3 ^ 40 * 1304736 * 2
def baseEnd_1304736 : Nat := 669956695224712448099635

theorem tailTrace_1304736 : CollatzResearch.WordTrace tailWord_1304736 prefixEnd_1304736 669956695224712448099635 := by
  unfold tailWord_1304736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23793815700585889006707031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31725087600781185342276041 23793815700585889006707031)
  ·
    refine ⟨35690723550878833510060547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23793815700585889006707031 35690723550878833510060547)
    ·
      refine ⟨53536085326318250265090821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35690723550878833510060547 53536085326318250265090821)
      ·
        refine ⟨10038015998684671924704529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53536085326318250265090821 10038015998684671924704529)
        ·
          refine ⟨7528511999013503943528397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10038015998684671924704529 7528511999013503943528397)
          ·
            refine ⟨2823191999630063978823149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7528511999013503943528397 2823191999630063978823149)
            ·
              refine ⟨1058696999861273992058681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2823191999630063978823149 1058696999861273992058681)
              ·
                refine ⟨794022749895955494044011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058696999861273992058681 794022749895955494044011)
                ·
                  refine ⟨1191034124843933241066017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794022749895955494044011 1191034124843933241066017)
                  ·
                    refine ⟨893275593632949930799513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1191034124843933241066017 893275593632949930799513)
                    ·
                      refine ⟨669956695224712448099635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 893275593632949930799513 669956695224712448099635)
                      ·
                        rfl

theorem cell23_1304736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_1304736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304736 prefixEnd_1304736 := by exact prefixLift 1304736
  have htrace : WordTrace (prefixWord ++ tailWord_1304736) baseStart_1304736 baseEnd_1304736 := by
    simpa [prefixWord, tailWord_1304736, baseEnd_1304736] using wordTrace_append hprefix tailTrace_1304736
  have hstable : (prefixWord ++ tailWord_1304736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304736).length < 2 ^ (prefixWord ++ tailWord_1304736).sum := by decide
  have hdescent : baseEnd_1304736 < baseStart_1304736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304746 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1304746 : Nat := 118140960795 + 1304746 * 2 ^ 59
def prefixEnd_1304746 : Nat := 4983230072969 + 3 ^ 40 * 1304746 * 2
def baseEnd_1304746 : Nat := 223320610010419136324863

theorem tailTrace_1304746 : CollatzResearch.WordTrace tailWord_1304746 prefixEnd_1304746 223320610010419136324863 := by
  unfold tailWord_1304746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11896999032783887430319523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31725330754090366480852061 11896999032783887430319523)
  ·
    refine ⟨17845498549175831145479285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11896999032783887430319523 17845498549175831145479285)
    ·
      refine ⟨1673015488985234169888683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17845498549175831145479285 1673015488985234169888683)
      ·
        refine ⟨2509523233477851254833025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673015488985234169888683 2509523233477851254833025)
        ·
          refine ⟨1882142425108388441124769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2509523233477851254833025 1882142425108388441124769)
          ·
            refine ⟨1411606818831291330843577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1882142425108388441124769 1411606818831291330843577)
            ·
              refine ⟨1058705114123468498132683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411606818831291330843577 1058705114123468498132683)
              ·
                refine ⟨1588057671185202747199025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058705114123468498132683 1588057671185202747199025)
                ·
                  refine ⟨1191043253388902060399269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1588057671185202747199025 1191043253388902060399269)
                  ·
                    refine ⟨223320610010419136324863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1191043253388902060399269 223320610010419136324863)
                    ·
                      rfl

theorem cell23_1304746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1304746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304746 prefixEnd_1304746 := by exact prefixLift 1304746
  have htrace : WordTrace (prefixWord ++ tailWord_1304746) baseStart_1304746 baseEnd_1304746 := by
    simpa [prefixWord, tailWord_1304746, baseEnd_1304746] using wordTrace_append hprefix tailTrace_1304746
  have hstable : (prefixWord ++ tailWord_1304746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304746).length < 2 ^ (prefixWord ++ tailWord_1304746).sum := by decide
  have hdescent : baseEnd_1304746 < baseStart_1304746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304751 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 8]
def baseStart_1304751 : Nat := 118140960795 + 1304751 * 2 ^ 59
def prefixEnd_1304751 : Nat := 4983230072969 + 3 ^ 40 * 1304751 * 2
def baseEnd_1304751 : Nat := 223321465811509963137355

theorem tailTrace_1304751 : CollatzResearch.WordTrace tailWord_1304751 prefixEnd_1304751 223321465811509963137355 := by
  unfold tailWord_1304751
  simp only [CollatzResearch.WordTrace]
  refine ⟨47588178496117435575210107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31725452330744957050140071 47588178496117435575210107)
  ·
    refine ⟨71382267744176153362815161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47588178496117435575210107 71382267744176153362815161)
    ·
      refine ⟨53536700808132115022111371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71382267744176153362815161 53536700808132115022111371)
      ·
        refine ⟨80305051212198172533167057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53536700808132115022111371 80305051212198172533167057)
        ·
          refine ⟨60228788409148629399875293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80305051212198172533167057 60228788409148629399875293)
          ·
            refine ⟨22585795653430736024953235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60228788409148629399875293 22585795653430736024953235)
            ·
              refine ⟨33878693480146104037429853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22585795653430736024953235 33878693480146104037429853)
              ·
                refine ⟨12704510055054789014036195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33878693480146104037429853 12704510055054789014036195)
                ·
                  refine ⟨19056765082582183521054293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12704510055054789014036195 19056765082582183521054293)
                  ·
                    refine ⟨223321465811509963137355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19056765082582183521054293 223321465811509963137355)
                    ·
                      rfl

theorem cell23_1304751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_1304751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304751 prefixEnd_1304751 := by exact prefixLift 1304751
  have htrace : WordTrace (prefixWord ++ tailWord_1304751) baseStart_1304751 baseEnd_1304751 := by
    simpa [prefixWord, tailWord_1304751, baseEnd_1304751] using wordTrace_append hprefix tailTrace_1304751
  have hstable : (prefixWord ++ tailWord_1304751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304751).length < 2 ^ (prefixWord ++ tailWord_1304751).sum := by decide
  have hdescent : baseEnd_1304751 < baseStart_1304751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304756 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_1304756 : Nat := 118140960795 + 1304756 * 2 ^ 59
def prefixEnd_1304756 : Nat := 4983230072969 + 3 ^ 40 * 1304756 * 2
def baseEnd_1304756 : Nat := 669966964837802369849543

theorem tailTrace_1304756 : CollatzResearch.WordTrace tailWord_1304756 prefixEnd_1304756 669966964837802369849543 := by
  unfold tailWord_1304756
  simp only [CollatzResearch.WordTrace]
  refine ⟨23794180430549660714571061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31725573907399547619428081 23794180430549660714571061)
  ·
    refine ⟨2230704415364030691991037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23794180430549660714571061 2230704415364030691991037)
    ·
      refine ⟨836514155761511509496639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2230704415364030691991037 836514155761511509496639)
      ·
        refine ⟨1254771233642267264244959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836514155761511509496639 1254771233642267264244959)
        ·
          refine ⟨1882156850463400896367439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254771233642267264244959 1882156850463400896367439)
          ·
            refine ⟨2823235275695101344551159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882156850463400896367439 2823235275695101344551159)
            ·
              refine ⟨4234852913542652016826739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823235275695101344551159 4234852913542652016826739)
              ·
                refine ⟨6352279370313978025240109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234852913542652016826739 6352279370313978025240109)
                ·
                  refine ⟨2382104763867741759465041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6352279370313978025240109 2382104763867741759465041)
                  ·
                    refine ⟨1786578572900806319598781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382104763867741759465041 1786578572900806319598781)
                    ·
                      refine ⟨669966964837802369849543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786578572900806319598781 669966964837802369849543)
                      ·
                        rfl

theorem cell23_1304756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_1304756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304756 prefixEnd_1304756 := by exact prefixLift 1304756
  have htrace : WordTrace (prefixWord ++ tailWord_1304756) baseStart_1304756 baseEnd_1304756 := by
    simpa [prefixWord, tailWord_1304756, baseEnd_1304756] using wordTrace_append hprefix tailTrace_1304756
  have hstable : (prefixWord ++ tailWord_1304756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304756).length < 2 ^ (prefixWord ++ tailWord_1304756).sum := by decide
  have hdescent : baseEnd_1304756 < baseStart_1304756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304762 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2]
def baseStart_1304762 : Nat := 118140960795 + 1304762 * 2 ^ 59
def prefixEnd_1304762 : Nat := 4983230072969 + 3 ^ 40 * 1304762 * 2
def baseEnd_1304762 : Nat := 669970045721729346374515

theorem tailTrace_1304762 : CollatzResearch.WordTrace tailWord_1304762 prefixEnd_1304762 669970045721729346374515 := by
  unfold tailWord_1304762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897144924769396113465135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31725719799385056302573693 11897144924769396113465135)
  ·
    refine ⟨17845717387154094170197703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11897144924769396113465135 17845717387154094170197703)
    ·
      refine ⟨26768576080731141255296555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17845717387154094170197703 26768576080731141255296555)
      ·
        refine ⟨40152864121096711882944833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26768576080731141255296555 40152864121096711882944833)
        ·
          refine ⟨30114648090822533912208625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40152864121096711882944833 30114648090822533912208625)
          ·
            refine ⟨22585986068116900434156469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30114648090822533912208625 22585986068116900434156469)
            ·
              refine ⟨2117436193885959415702169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22585986068116900434156469 2117436193885959415702169)
              ·
                refine ⟨1588077145414469561776627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117436193885959415702169 1588077145414469561776627)
                ·
                  refine ⟨2382115718121704342664941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588077145414469561776627 2382115718121704342664941)
                  ·
                    refine ⟨893293394295639128499353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382115718121704342664941 893293394295639128499353)
                    ·
                      refine ⟨669970045721729346374515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 893293394295639128499353 669970045721729346374515)
                      ·
                        rfl

theorem cell23_1304762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_1304762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304762 prefixEnd_1304762 := by exact prefixLift 1304762
  have htrace : WordTrace (prefixWord ++ tailWord_1304762) baseStart_1304762 baseEnd_1304762 := by
    simpa [prefixWord, tailWord_1304762, baseEnd_1304762] using wordTrace_append hprefix tailTrace_1304762
  have hstable : (prefixWord ++ tailWord_1304762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304762).length < 2 ^ (prefixWord ++ tailWord_1304762).sum := by decide
  have hdescent : baseEnd_1304762 < baseStart_1304762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304771 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1304771 : Nat := 118140960795 + 1304771 * 2 ^ 59
def prefixEnd_1304771 : Nat := 4983230072969 + 3 ^ 40 * 1304771 * 2
def baseEnd_1304771 : Nat := 669974667047619811161973

theorem tailTrace_1304771 : CollatzResearch.WordTrace tailWord_1304771 prefixEnd_1304771 669974667047619811161973 := by
  unfold tailWord_1304771
  simp only [CollatzResearch.WordTrace]
  refine ⟨47588907956044978990938167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31725938637363319327292111 47588907956044978990938167)
  ·
    refine ⟨71383361934067468486407251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47588907956044978990938167 71383361934067468486407251)
    ·
      refine ⟨107075042901101202729610877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71383361934067468486407251 107075042901101202729610877)
      ·
        refine ⟨40153141087912951023604079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107075042901101202729610877 40153141087912951023604079)
        ·
          refine ⟨60229711631869426535406119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40153141087912951023604079 60229711631869426535406119)
          ·
            refine ⟨90344567447804139803109179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60229711631869426535406119 90344567447804139803109179)
            ·
              refine ⟨135516851171706209704663769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90344567447804139803109179 135516851171706209704663769)
              ·
                refine ⟨101637638378779657278497827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135516851171706209704663769 101637638378779657278497827)
                ·
                  refine ⟨152456457568169485917746741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101637638378779657278497827 152456457568169485917746741)
                  ·
                    refine ⟨14292792897015889304788757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 152456457568169485917746741 14292792897015889304788757)
                    ·
                      refine ⟨669974667047619811161973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14292792897015889304788757 669974667047619811161973)
                      ·
                        rfl

theorem cell23_1304771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1304771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304771 prefixEnd_1304771 := by exact prefixLift 1304771
  have htrace : WordTrace (prefixWord ++ tailWord_1304771) baseStart_1304771 baseEnd_1304771 := by
    simpa [prefixWord, tailWord_1304771, baseEnd_1304771] using wordTrace_append hprefix tailTrace_1304771
  have hstable : (prefixWord ++ tailWord_1304771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304771).length < 2 ^ (prefixWord ++ tailWord_1304771).sum := by decide
  have hdescent : baseEnd_1304771 < baseStart_1304771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304778 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1304778 : Nat := 118140960795 + 1304778 * 2 ^ 59
def prefixEnd_1304778 : Nat := 4983230072969 + 3 ^ 40 * 1304778 * 2
def baseEnd_1304778 : Nat := 669978261412201283774441

theorem tailTrace_1304778 : CollatzResearch.WordTrace tailWord_1304778 prefixEnd_1304778 669978261412201283774441 := by
  unfold tailWord_1304778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897290816754904796610747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31726108844679746124295325 11897290816754904796610747)
  ·
    refine ⟨17845936225132357194916121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11897290816754904796610747 17845936225132357194916121)
    ·
      refine ⟨13384452168849267896187091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17845936225132357194916121 13384452168849267896187091)
      ·
        refine ⟨20076678253273901844280637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13384452168849267896187091 20076678253273901844280637)
        ·
          refine ⟨7528754344977713191605239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20076678253273901844280637 7528754344977713191605239)
          ·
            refine ⟨11293131517466569787407859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528754344977713191605239 11293131517466569787407859)
            ·
              refine ⟨16939697276199854681111789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11293131517466569787407859 16939697276199854681111789)
              ·
                refine ⟨6352386478574945505416921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16939697276199854681111789 6352386478574945505416921)
                ·
                  refine ⟨4764289858931209129062691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352386478574945505416921 4764289858931209129062691)
                  ·
                    refine ⟨7146434788396813693594037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764289858931209129062691 7146434788396813693594037)
                    ·
                      refine ⟨669978261412201283774441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7146434788396813693594037 669978261412201283774441)
                      ·
                        rfl

theorem cell23_1304778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1304778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304778 prefixEnd_1304778 := by exact prefixLift 1304778
  have htrace : WordTrace (prefixWord ++ tailWord_1304778) baseStart_1304778 baseEnd_1304778 := by
    simpa [prefixWord, tailWord_1304778, baseEnd_1304778] using wordTrace_append hprefix tailTrace_1304778
  have hstable : (prefixWord ++ tailWord_1304778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304778).length < 2 ^ (prefixWord ++ tailWord_1304778).sum := by decide
  have hdescent : baseEnd_1304778 < baseStart_1304778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304805 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1304805 : Nat := 118140960795 + 1304805 * 2 ^ 59
def prefixEnd_1304805 : Nat := 4983230072969 + 3 ^ 40 * 1304805 * 2
def baseEnd_1304805 : Nat := 669992125389872678136817

theorem tailTrace_1304805 : CollatzResearch.WordTrace tailWord_1304805 prefixEnd_1304805 669992125389872678136817 := by
  unfold tailWord_1304805
  simp only [CollatzResearch.WordTrace]
  refine ⟨47590148037921802797675869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31726765358614535198450579 47590148037921802797675869)
  ·
    refine ⟨17846305514220676049128451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47590148037921802797675869 17846305514220676049128451)
    ·
      refine ⟨26769458271331014073692677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17846305514220676049128451 26769458271331014073692677)
      ·
        refine ⟨5019273425874565138817377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26769458271331014073692677 5019273425874565138817377)
        ·
          refine ⟨3764455069405923854113033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5019273425874565138817377 3764455069405923854113033)
          ·
            refine ⟨2823341302054442890584775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3764455069405923854113033 2823341302054442890584775)
            ·
              refine ⟨4235011953081664335877163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823341302054442890584775 4235011953081664335877163)
              ·
                refine ⟨6352517929622496503815745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235011953081664335877163 6352517929622496503815745)
                ·
                  refine ⟨4764388447216872377861809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352517929622496503815745 4764388447216872377861809)
                  ·
                    refine ⟨3573291335412654283396357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4764388447216872377861809 3573291335412654283396357)
                    ·
                      refine ⟨669992125389872678136817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3573291335412654283396357 669992125389872678136817)
                      ·
                        rfl

theorem cell23_1304805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1304805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304805 prefixEnd_1304805 := by exact prefixLift 1304805
  have htrace : WordTrace (prefixWord ++ tailWord_1304805) baseStart_1304805 baseEnd_1304805 := by
    simpa [prefixWord, tailWord_1304805, baseEnd_1304805] using wordTrace_append hprefix tailTrace_1304805
  have hstable : (prefixWord ++ tailWord_1304805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304805).length < 2 ^ (prefixWord ++ tailWord_1304805).sum := by decide
  have hdescent : baseEnd_1304805 < baseStart_1304805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304862 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1304862 : Nat := 118140960795 + 1304862 * 2 ^ 59
def prefixEnd_1304862 : Nat := 4983230072969 + 3 ^ 40 * 1304862 * 2
def baseEnd_1304862 : Nat := 223340464595726318374685

theorem tailTrace_1304862 : CollatzResearch.WordTrace tailWord_1304862 prefixEnd_1304862 223340464595726318374685 := by
  unfold tailWord_1304862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949028374839412691562605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31728151332476867688333893 5949028374839412691562605)
  ·
    refine ⟨2230885640564779759335977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5949028374839412691562605 2230885640564779759335977)
    ·
      refine ⟨1673164230423584819501983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2230885640564779759335977 1673164230423584819501983)
      ·
        refine ⟨2509746345635377229252975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673164230423584819501983 2509746345635377229252975)
        ·
          refine ⟨3764619518453065843879463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509746345635377229252975 3764619518453065843879463)
          ·
            refine ⟨5646929277679598765819195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764619518453065843879463 5646929277679598765819195)
            ·
              refine ⟨8470393916519398148728793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646929277679598765819195 8470393916519398148728793)
              ·
                refine ⟨6352795437389548611546595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8470393916519398148728793 6352795437389548611546595)
                ·
                  refine ⟨9529193156084322917319893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6352795437389548611546595 9529193156084322917319893)
                  ·
                    refine ⟨223340464595726318374685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9529193156084322917319893 223340464595726318374685)
                    ·
                      rfl

theorem cell23_1304862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1304862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304862 prefixEnd_1304862 := by exact prefixLift 1304862
  have htrace : WordTrace (prefixWord ++ tailWord_1304862) baseStart_1304862 baseEnd_1304862 := by
    simpa [prefixWord, tailWord_1304862, baseEnd_1304862] using wordTrace_append hprefix tailTrace_1304862
  have hstable : (prefixWord ++ tailWord_1304862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304862).length < 2 ^ (prefixWord ++ tailWord_1304862).sum := by decide
  have hdescent : baseEnd_1304862 < baseStart_1304862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304885 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1304885 : Nat := 118140960795 + 1304885 * 2 ^ 59
def prefixEnd_1304885 : Nat := 4983230072969 + 3 ^ 40 * 1304885 * 2
def baseEnd_1304885 : Nat := 670033203842232365136449

theorem tailTrace_1304885 : CollatzResearch.WordTrace tailWord_1304885 prefixEnd_1304885 670033203842232365136449 := by
  unfold tailWord_1304885
  simp only [CollatzResearch.WordTrace]
  refine ⟨47593065877631976460588109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31728710585087984307058739 47593065877631976460588109)
  ·
    refine ⟨17847399704111991172720541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47593065877631976460588109 17847399704111991172720541)
    ·
      refine ⟨6692774889041996689770203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17847399704111991172720541 6692774889041996689770203)
      ·
        refine ⟨10039162333562995034655305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6692774889041996689770203 10039162333562995034655305)
        ·
          refine ⟨7529371750172246275991479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10039162333562995034655305 7529371750172246275991479)
          ·
            refine ⟨11294057625258369413987219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529371750172246275991479 11294057625258369413987219)
            ·
              refine ⟨16941086437887554120980829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11294057625258369413987219 16941086437887554120980829)
              ·
                refine ⟨6352907414207832795367811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16941086437887554120980829 6352907414207832795367811)
                ·
                  refine ⟨9529361121311749193051717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6352907414207832795367811 9529361121311749193051717)
                  ·
                    refine ⟨1786755210245952973697197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9529361121311749193051717 1786755210245952973697197)
                    ·
                      refine ⟨670033203842232365136449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786755210245952973697197 670033203842232365136449)
                      ·
                        rfl

theorem cell23_1304885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1304885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304885 prefixEnd_1304885 := by exact prefixLift 1304885
  have htrace : WordTrace (prefixWord ++ tailWord_1304885) baseStart_1304885 baseEnd_1304885 := by
    simpa [prefixWord, tailWord_1304885, baseEnd_1304885] using wordTrace_append hprefix tailTrace_1304885
  have hstable : (prefixWord ++ tailWord_1304885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304885).length < 2 ^ (prefixWord ++ tailWord_1304885).sum := by decide
  have hdescent : baseEnd_1304885 < baseStart_1304885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304888 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 8]
def baseStart_1304888 : Nat := 118140960795 + 1304888 * 2 ^ 59
def prefixEnd_1304888 : Nat := 4983230072969 + 3 ^ 40 * 1304888 * 2
def baseEnd_1304888 : Nat := 74448304920466205933215

theorem tailTrace_1304888 : CollatzResearch.WordTrace tailWord_1304888 prefixEnd_1304888 74448304920466205933215 := by
  unfold tailWord_1304888
  simp only [CollatzResearch.WordTrace]
  refine ⟨23796587648310553986473659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31728783531080738648631545 23796587648310553986473659)
  ·
    refine ⟨35694881472465830979710489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23796587648310553986473659 35694881472465830979710489)
    ·
      refine ⟨26771161104349373234782867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35694881472465830979710489 26771161104349373234782867)
      ·
        refine ⟨40156741656524059852174301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26771161104349373234782867 40156741656524059852174301)
        ·
          refine ⟨15058778121196522444565363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40156741656524059852174301 15058778121196522444565363)
          ·
            refine ⟨22588167181794783666848045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15058778121196522444565363 22588167181794783666848045)
            ·
              refine ⟨8470562693173043875068017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22588167181794783666848045 8470562693173043875068017)
              ·
                refine ⟨6352922019879782906301013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8470562693173043875068017 6352922019879782906301013)
                ·
                  refine ⟨74448304920466205933215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6352922019879782906301013 74448304920466205933215)
                  ·
                    rfl

theorem cell23_1304888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_1304888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304888 prefixEnd_1304888 := by exact prefixLift 1304888
  have htrace : WordTrace (prefixWord ++ tailWord_1304888) baseStart_1304888 baseEnd_1304888 := by
    simpa [prefixWord, tailWord_1304888, baseEnd_1304888] using wordTrace_append hprefix tailTrace_1304888
  have hstable : (prefixWord ++ tailWord_1304888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304888).length < 2 ^ (prefixWord ++ tailWord_1304888).sum := by decide
  have hdescent : baseEnd_1304888 < baseStart_1304888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304932 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_1304932 : Nat := 118140960795 + 1304932 * 2 ^ 59
def prefixEnd_1304932 : Nat := 4983230072969 + 3 ^ 40 * 1304932 * 2
def baseEnd_1304932 : Nat := 670057337432993681248733

theorem tailTrace_1304932 : CollatzResearch.WordTrace tailWord_1304932 prefixEnd_1304932 670057337432993681248733 := by
  unfold tailWord_1304932
  simp only [CollatzResearch.WordTrace]
  refine ⟨23797390054230851743774525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31729853405641135658366033 23797390054230851743774525)
  ·
    refine ⟨8924021270336569403915447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23797390054230851743774525 8924021270336569403915447)
    ·
      refine ⟨13386031905504854105873171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8924021270336569403915447 13386031905504854105873171)
      ·
        refine ⟨20079047858257281158809757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13386031905504854105873171 20079047858257281158809757)
        ·
          refine ⟨7529642946846480434553659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20079047858257281158809757 7529642946846480434553659)
          ·
            refine ⟨11294464420269720651830489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529642946846480434553659 11294464420269720651830489)
            ·
              refine ⟨8470848315202290488872867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11294464420269720651830489 8470848315202290488872867)
              ·
                refine ⟨12706272472803435733309301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470848315202290488872867 12706272472803435733309301)
                ·
                  refine ⟨1191213044325322099997747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12706272472803435733309301 1191213044325322099997747)
                  ·
                    refine ⟨1786819566487983149996621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1191213044325322099997747 1786819566487983149996621)
                    ·
                      refine ⟨670057337432993681248733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786819566487983149996621 670057337432993681248733)
                      ·
                        rfl

theorem cell23_1304932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_1304932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304932 prefixEnd_1304932 := by exact prefixLift 1304932
  have htrace : WordTrace (prefixWord ++ tailWord_1304932) baseStart_1304932 baseEnd_1304932 := by
    simpa [prefixWord, tailWord_1304932, baseEnd_1304932] using wordTrace_append hprefix tailTrace_1304932
  have hstable : (prefixWord ++ tailWord_1304932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304932).length < 2 ^ (prefixWord ++ tailWord_1304932).sum := by decide
  have hdescent : baseEnd_1304932 < baseStart_1304932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304992 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1304992 : Nat := 118140960795 + 1304992 * 2 ^ 59
def prefixEnd_1304992 : Nat := 4983230072969 + 3 ^ 40 * 1304992 * 2
def baseEnd_1304992 : Nat := 670088146272263446498457

theorem tailTrace_1304992 : CollatzResearch.WordTrace tailWord_1304992 prefixEnd_1304992 670088146272263446498457 := by
  unfold tailWord_1304992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23798484244122166867366615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31731312325496222489822153 23798484244122166867366615)
  ·
    refine ⟨35697726366183250301049923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23798484244122166867366615 35697726366183250301049923)
    ·
      refine ⟨53546589549274875451574885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35697726366183250301049923 53546589549274875451574885)
      ·
        refine ⟨10039985540489039147170291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53546589549274875451574885 10039985540489039147170291)
        ·
          refine ⟨15059978310733558720755437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10039985540489039147170291 15059978310733558720755437)
          ·
            refine ⟨5647491866525084520283289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15059978310733558720755437 5647491866525084520283289)
            ·
              refine ⟨4235618899893813390212467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5647491866525084520283289 4235618899893813390212467)
              ·
                refine ⟨6353428349840720085318701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235618899893813390212467 6353428349840720085318701)
                ·
                  refine ⟨2382535631190270031994513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6353428349840720085318701 2382535631190270031994513)
                  ·
                    refine ⟨1786901723392702523995885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382535631190270031994513 1786901723392702523995885)
                    ·
                      refine ⟨670088146272263446498457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786901723392702523995885 670088146272263446498457)
                      ·
                        rfl

theorem cell23_1304992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1304992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304992 prefixEnd_1304992 := by exact prefixLift 1304992
  have htrace : WordTrace (prefixWord ++ tailWord_1304992) baseStart_1304992 baseEnd_1304992 := by
    simpa [prefixWord, tailWord_1304992, baseEnd_1304992] using wordTrace_append hprefix tailTrace_1304992
  have hstable : (prefixWord ++ tailWord_1304992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304992).length < 2 ^ (prefixWord ++ tailWord_1304992).sum := by decide
  have hdescent : baseEnd_1304992 < baseStart_1304992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304993 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1304993 : Nat := 118140960795 + 1304993 * 2 ^ 59
def prefixEnd_1304993 : Nat := 4983230072969 + 3 ^ 40 * 1304993 * 2
def baseEnd_1304993 : Nat := 670088659752917942585953

theorem tailTrace_1304993 : CollatzResearch.WordTrace tailWord_1304993 prefixEnd_1304993 670088659752917942585953 := by
  unfold tailWord_1304993
  simp only [CollatzResearch.WordTrace]
  refine ⟨47597004961240710905519633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31731336640827140603679755 47597004961240710905519633)
  ·
    refine ⟨35697753720930533179139725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47597004961240710905519633 35697753720930533179139725)
    ·
      refine ⟨13386657645348949942177397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35697753720930533179139725 13386657645348949942177397)
      ·
        refine ⟨1254999154251464057079131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13386657645348949942177397 1254999154251464057079131)
        ·
          refine ⟨1882498731377196085618697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254999154251464057079131 1882498731377196085618697)
          ·
            refine ⟨1411874048532897064214023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1882498731377196085618697 1411874048532897064214023)
            ·
              refine ⟨2117811072799345596321035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411874048532897064214023 2117811072799345596321035)
              ·
                refine ⟨3176716609199018394481553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117811072799345596321035 3176716609199018394481553)
                ·
                  refine ⟨2382537456899263795861165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176716609199018394481553 2382537456899263795861165)
                  ·
                    refine ⟨893451546337223923447937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382537456899263795861165 893451546337223923447937)
                    ·
                      refine ⟨670088659752917942585953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 893451546337223923447937 670088659752917942585953)
                      ·
                        rfl

theorem cell23_1304993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1304993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1304993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1304993 prefixEnd_1304993 := by exact prefixLift 1304993
  have htrace : WordTrace (prefixWord ++ tailWord_1304993) baseStart_1304993 baseEnd_1304993 := by
    simpa [prefixWord, tailWord_1304993, baseEnd_1304993] using wordTrace_append hprefix tailTrace_1304993
  have hstable : (prefixWord ++ tailWord_1304993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304993).length < 2 ^ (prefixWord ++ tailWord_1304993).sum := by decide
  have hdescent : baseEnd_1304993 < baseStart_1304993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305009 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1305009 : Nat := 118140960795 + 1305009 * 2 ^ 59
def prefixEnd_1305009 : Nat := 4983230072969 + 3 ^ 40 * 1305009 * 2
def baseEnd_1305009 : Nat := 670096875443389879985879

theorem tailTrace_1305009 : CollatzResearch.WordTrace tailWord_1305009 prefixEnd_1305009 670096875443389879985879 := by
  unfold tailWord_1305009
  simp only [CollatzResearch.WordTrace]
  refine ⟨47597588529182745638102081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31731725686121830425401387 47597588529182745638102081)
  ·
    refine ⟨35698191396887059228576561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47597588529182745638102081 35698191396887059228576561)
    ·
      refine ⟨26773643547665294421432421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35698191396887059228576561 26773643547665294421432421)
      ·
        refine ⟨5020058165187242704018579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26773643547665294421432421 5020058165187242704018579)
        ·
          refine ⟨7530087247780864056027869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020058165187242704018579 7530087247780864056027869)
          ·
            refine ⟨2823782717917824021010451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7530087247780864056027869 2823782717917824021010451)
            ·
              refine ⟨4235674076876736031515677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823782717917824021010451 4235674076876736031515677)
              ·
                refine ⟨1588377778828776011818379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4235674076876736031515677 1588377778828776011818379)
                ·
                  refine ⟨2382566668243164017727569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588377778828776011818379 2382566668243164017727569)
                  ·
                    refine ⟨1786925001182373013295677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382566668243164017727569 1786925001182373013295677)
                    ·
                      refine ⟨670096875443389879985879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786925001182373013295677 670096875443389879985879)
                      ·
                        rfl

theorem cell23_1305009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1305009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305009 prefixEnd_1305009 := by exact prefixLift 1305009
  have htrace : WordTrace (prefixWord ++ tailWord_1305009) baseStart_1305009 baseEnd_1305009 := by
    simpa [prefixWord, tailWord_1305009, baseEnd_1305009] using wordTrace_append hprefix tailTrace_1305009
  have hstable : (prefixWord ++ tailWord_1305009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305009).length < 2 ^ (prefixWord ++ tailWord_1305009).sum := by decide
  have hdescent : baseEnd_1305009 < baseStart_1305009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305022 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1305022 : Nat := 118140960795 + 1305022 * 2 ^ 59
def prefixEnd_1305022 : Nat := 4983230072969 + 3 ^ 40 * 1305022 * 2
def baseEnd_1305022 : Nat := 670103550691898329123319

theorem tailTrace_1305022 : CollatzResearch.WordTrace tailWord_1305022 prefixEnd_1305022 670103550691898329123319 := by
  unfold tailWord_1305022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949757834766956107290665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31732041785423765905550213 5949757834766956107290665)
  ·
    refine ⟨4462318376075217080467999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5949757834766956107290665 4462318376075217080467999)
    ·
      refine ⟨6693477564112825620701999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4462318376075217080467999 6693477564112825620701999)
      ·
        refine ⟨10040216346169238431052999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6693477564112825620701999 10040216346169238431052999)
        ·
          refine ⟨15060324519253857646579499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10040216346169238431052999 15060324519253857646579499)
          ·
            refine ⟨22590486778880786469869249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15060324519253857646579499 22590486778880786469869249)
            ·
              refine ⟨16942865084160589852401937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22590486778880786469869249 16942865084160589852401937)
              ·
                refine ⟨12707148813120442389301453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16942865084160589852401937 12707148813120442389301453)
                ·
                  refine ⟨4765180804920165895988045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12707148813120442389301453 4765180804920165895988045)
                  ·
                    refine ⟨1786942801845062210995517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4765180804920165895988045 1786942801845062210995517)
                    ·
                      refine ⟨670103550691898329123319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1786942801845062210995517 670103550691898329123319)
                      ·
                        rfl

theorem cell23_1305022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1305022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305022 prefixEnd_1305022 := by exact prefixLift 1305022
  have htrace : WordTrace (prefixWord ++ tailWord_1305022) baseStart_1305022 baseEnd_1305022 := by
    simpa [prefixWord, tailWord_1305022, baseEnd_1305022] using wordTrace_append hprefix tailTrace_1305022
  have hstable : (prefixWord ++ tailWord_1305022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305022).length < 2 ^ (prefixWord ++ tailWord_1305022).sum := by decide
  have hdescent : baseEnd_1305022 < baseStart_1305022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305036 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1305036 : Nat := 118140960795 + 1305036 * 2 ^ 59
def prefixEnd_1305036 : Nat := 4983230072969 + 3 ^ 40 * 1305036 * 2
def baseEnd_1305036 : Nat := 670110739421061274348255

theorem tailTrace_1305036 : CollatzResearch.WordTrace tailWord_1305036 prefixEnd_1305036 670110739421061274348255 := by
  unfold tailWord_1305036
  simp only [CollatzResearch.WordTrace]
  refine ⟨23799286650042464624667481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31732382200056619499556641 23799286650042464624667481)
  ·
    refine ⟨17849464987531848468500611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23799286650042464624667481 17849464987531848468500611)
    ·
      refine ⟨26774197481297772702750917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17849464987531848468500611 26774197481297772702750917)
      ·
        refine ⟨5020162027743332381765797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26774197481297772702750917 5020162027743332381765797)
        ·
          refine ⟨941280380201874821581087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5020162027743332381765797 941280380201874821581087)
          ·
            refine ⟨1411920570302812232371631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941280380201874821581087 1411920570302812232371631)
            ·
              refine ⟨2117880855454218348557447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411920570302812232371631 2117880855454218348557447)
              ·
                refine ⟨3176821283181327522836171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117880855454218348557447 3176821283181327522836171)
                ·
                  refine ⟨4765231924771991284254257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176821283181327522836171 4765231924771991284254257)
                  ·
                    refine ⟨3573923943578993463190693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4765231924771991284254257 3573923943578993463190693)
                    ·
                      refine ⟨670110739421061274348255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3573923943578993463190693 670110739421061274348255)
                      ·
                        rfl

theorem cell23_1305036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1305036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305036 prefixEnd_1305036 := by exact prefixLift 1305036
  have htrace : WordTrace (prefixWord ++ tailWord_1305036) baseStart_1305036 baseEnd_1305036 := by
    simpa [prefixWord, tailWord_1305036, baseEnd_1305036] using wordTrace_append hprefix tailTrace_1305036
  have hstable : (prefixWord ++ tailWord_1305036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305036).length < 2 ^ (prefixWord ++ tailWord_1305036).sum := by decide
  have hdescent : baseEnd_1305036 < baseStart_1305036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305066 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_1305066 : Nat := 118140960795 + 1305066 * 2 ^ 59
def prefixEnd_1305066 : Nat := 4983230072969 + 3 ^ 40 * 1305066 * 2
def baseEnd_1305066 : Nat := 670126143840696156973117

theorem tailTrace_1305066 : CollatzResearch.WordTrace tailWord_1305066 prefixEnd_1305066 670126143840696156973117 := by
  unfold tailWord_1305066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899916872494061093231763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31733111659984162915284701 11899916872494061093231763)
  ·
    refine ⟨17849875308741091639847645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899916872494061093231763 17849875308741091639847645)
    ·
      refine ⟨6693703240777909364942867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17849875308741091639847645 6693703240777909364942867)
      ·
        refine ⟨10040554861166864047414301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6693703240777909364942867 10040554861166864047414301)
        ·
          refine ⟨3765208072937574017780363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10040554861166864047414301 3765208072937574017780363)
          ·
            refine ⟨5647812109406361026670545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765208072937574017780363 5647812109406361026670545)
            ·
              refine ⟨4235859082054770770002909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5647812109406361026670545 4235859082054770770002909)
              ·
                refine ⟨1588447155770539038751091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4235859082054770770002909 1588447155770539038751091)
                ·
                  refine ⟨2382670733655808558126637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588447155770539038751091 2382670733655808558126637)
                  ·
                    refine ⟨893501525120928209297489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382670733655808558126637 893501525120928209297489)
                    ·
                      refine ⟨670126143840696156973117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 893501525120928209297489 670126143840696156973117)
                      ·
                        rfl

theorem cell23_1305066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_1305066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305066 prefixEnd_1305066 := by exact prefixLift 1305066
  have htrace : WordTrace (prefixWord ++ tailWord_1305066) baseStart_1305066 baseEnd_1305066 := by
    simpa [prefixWord, tailWord_1305066, baseEnd_1305066] using wordTrace_append hprefix tailTrace_1305066
  have hstable : (prefixWord ++ tailWord_1305066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305066).length < 2 ^ (prefixWord ++ tailWord_1305066).sum := by decide
  have hdescent : baseEnd_1305066 < baseStart_1305066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305152 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_1305152 : Nat := 118140960795 + 1305152 * 2 ^ 59
def prefixEnd_1305152 : Nat := 4983230072969 + 3 ^ 40 * 1305152 * 2
def baseEnd_1305152 : Nat := 670170303176982820497721

theorem tailTrace_1305152 : CollatzResearch.WordTrace tailWord_1305152 prefixEnd_1305152 670170303176982820497721 := by
  unfold tailWord_1305152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23801402083832340530278855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31735202778443120707038473 23801402083832340530278855)
  ·
    refine ⟨35702103125748510795418283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23801402083832340530278855 35702103125748510795418283)
    ·
      refine ⟨53553154688622766193127425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35702103125748510795418283 53553154688622766193127425)
      ·
        refine ⟨40164866016467074644845569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53553154688622766193127425 40164866016467074644845569)
        ·
          refine ⟨30123649512350305983634177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40164866016467074644845569 30123649512350305983634177)
          ·
            refine ⟨22592737134262729487725633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30123649512350305983634177 22592737134262729487725633)
            ·
              refine ⟨16944552850697047115794225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22592737134262729487725633 16944552850697047115794225)
              ·
                refine ⟨12708414638022785336845669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16944552850697047115794225 12708414638022785336845669)
                ·
                  refine ⟨2382827744629272250658563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12708414638022785336845669 2382827744629272250658563)
                  ·
                    refine ⟨3574241616943908375987845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2382827744629272250658563 3574241616943908375987845)
                    ·
                      refine ⟨670170303176982820497721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3574241616943908375987845 670170303176982820497721)
                      ·
                        rfl

theorem cell23_1305152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_1305152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305152 prefixEnd_1305152 := by exact prefixLift 1305152
  have htrace : WordTrace (prefixWord ++ tailWord_1305152) baseStart_1305152 baseEnd_1305152 := by
    simpa [prefixWord, tailWord_1305152, baseEnd_1305152] using wordTrace_append hprefix tailTrace_1305152
  have hstable : (prefixWord ++ tailWord_1305152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305152).length < 2 ^ (prefixWord ++ tailWord_1305152).sum := by decide
  have hdescent : baseEnd_1305152 < baseStart_1305152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305169 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_1305169 : Nat := 118140960795 + 1305169 * 2 ^ 59
def prefixEnd_1305169 : Nat := 4983230072969 + 3 ^ 40 * 1305169 * 2
def baseEnd_1305169 : Nat := 670179032348109253985143

theorem tailTrace_1305169 : CollatzResearch.WordTrace tailWord_1305169 prefixEnd_1305169 670179032348109253985143 := by
  unfold tailWord_1305169
  simp only [CollatzResearch.WordTrace]
  refine ⟨47603424208603092963926561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31735616139068728642617707 47603424208603092963926561)
  ·
    refine ⟨35702568156452319722944921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47603424208603092963926561 35702568156452319722944921)
    ·
      refine ⟨26776926117339239792208691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35702568156452319722944921 26776926117339239792208691)
      ·
        refine ⟨40165389176008859688313037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26776926117339239792208691 40165389176008859688313037)
        ·
          refine ⟨15062020941003322383117389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40165389176008859688313037 15062020941003322383117389)
          ·
            refine ⟨5648257852876245893669021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15062020941003322383117389 5648257852876245893669021)
            ·
              refine ⟨2118096694828592210125883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5648257852876245893669021 2118096694828592210125883)
              ·
                refine ⟨3177145042242888315188825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118096694828592210125883 3177145042242888315188825)
                ·
                  refine ⟨2382858781682166236391619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177145042242888315188825 2382858781682166236391619)
                  ·
                    refine ⟨3574288172523249354587429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2382858781682166236391619 3574288172523249354587429)
                    ·
                      refine ⟨670179032348109253985143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3574288172523249354587429 670179032348109253985143)
                      ·
                        rfl

theorem cell23_1305169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_1305169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305169 prefixEnd_1305169 := by exact prefixLift 1305169
  have htrace : WordTrace (prefixWord ++ tailWord_1305169) baseStart_1305169 baseEnd_1305169 := by
    simpa [prefixWord, tailWord_1305169, baseEnd_1305169] using wordTrace_append hprefix tailTrace_1305169
  have hstable : (prefixWord ++ tailWord_1305169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305169).length < 2 ^ (prefixWord ++ tailWord_1305169).sum := by decide
  have hdescent : baseEnd_1305169 < baseStart_1305169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305196 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_1305196 : Nat := 118140960795 + 1305196 * 2 ^ 59
def prefixEnd_1305196 : Nat := 4983230072969 + 3 ^ 40 * 1305196 * 2
def baseEnd_1305196 : Nat := 223397632108593549449173

theorem tailTrace_1305196 : CollatzResearch.WordTrace tailWord_1305196 prefixEnd_1305196 223397632108593549449173 := by
  unfold tailWord_1305196
  simp only [CollatzResearch.WordTrace]
  refine ⟨23802204489752638287579721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31736272653003517716772961 23802204489752638287579721)
  ·
    refine ⟨17851653367314478715684791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23802204489752638287579721 17851653367314478715684791)
    ·
      refine ⟨26777480050971718073527187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17851653367314478715684791 26777480050971718073527187)
      ·
        refine ⟨40166220076457577110290781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26777480050971718073527187 40166220076457577110290781)
        ·
          refine ⟨15062332528671591416359043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40166220076457577110290781 15062332528671591416359043)
          ·
            refine ⟨22593498793007387124538565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15062332528671591416359043 22593498793007387124538565)
            ·
              refine ⟨4236281023688885085850981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22593498793007387124538565 4236281023688885085850981)
              ·
                refine ⟨794302691941665953597059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4236281023688885085850981 794302691941665953597059)
                ·
                  refine ⟨1191454037912498930395589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794302691941665953597059 1191454037912498930395589)
                  ·
                    refine ⟨223397632108593549449173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1191454037912498930395589 223397632108593549449173)
                    ·
                      rfl

theorem cell23_1305196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_1305196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305196 prefixEnd_1305196 := by exact prefixLift 1305196
  have htrace : WordTrace (prefixWord ++ tailWord_1305196) baseStart_1305196 baseEnd_1305196 := by
    simpa [prefixWord, tailWord_1305196, baseEnd_1305196] using wordTrace_append hprefix tailTrace_1305196
  have hstable : (prefixWord ++ tailWord_1305196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305196).length < 2 ^ (prefixWord ++ tailWord_1305196).sum := by decide
  have hdescent : baseEnd_1305196 < baseStart_1305196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305239 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 1, 5]
def baseStart_1305239 : Nat := 118140960795 + 1305239 * 2 ^ 59
def prefixEnd_1305239 : Nat := 4983230072969 + 3 ^ 40 * 1305239 * 2
def baseEnd_1305239 : Nat := 223404991997974660036607

theorem tailTrace_1305239 : CollatzResearch.WordTrace tailWord_1305239 prefixEnd_1305239 223404991997974660036607 := by
  unfold tailWord_1305239
  simp only [CollatzResearch.WordTrace]
  refine ⟨47605977318349494918974771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31737318212232996612649847 47605977318349494918974771)
  ·
    refine ⟨71408965977524242378462157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47605977318349494918974771 71408965977524242378462157)
    ·
      refine ⟨26778362241571590891923309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71408965977524242378462157 26778362241571590891923309)
      ·
        refine ⟨10041885840589346584471241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26778362241571590891923309 10041885840589346584471241)
        ·
          refine ⟨7531414380442009938353431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10041885840589346584471241 7531414380442009938353431)
          ·
            refine ⟨11297121570663014907530147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531414380442009938353431 11297121570663014907530147)
            ·
              refine ⟨16945682355994522361295221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11297121570663014907530147 16945682355994522361295221)
              ·
                refine ⟨1588657720874486471371427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16945682355994522361295221 1588657720874486471371427)
                ·
                  refine ⟨2382986581311729707057141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588657720874486471371427 2382986581311729707057141)
                  ·
                    refine ⟨223404991997974660036607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2382986581311729707057141 223404991997974660036607)
                    ·
                      rfl

theorem cell23_1305239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_1305239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305239 prefixEnd_1305239 := by exact prefixLift 1305239
  have htrace : WordTrace (prefixWord ++ tailWord_1305239) baseStart_1305239 baseEnd_1305239 := by
    simpa [prefixWord, tailWord_1305239, baseEnd_1305239] using wordTrace_append hprefix tailTrace_1305239
  have hstable : (prefixWord ++ tailWord_1305239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305239).length < 2 ^ (prefixWord ++ tailWord_1305239).sum := by decide
  have hdescent : baseEnd_1305239 < baseStart_1305239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305326 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1305326 : Nat := 118140960795 + 1305326 * 2 ^ 59
def prefixEnd_1305326 : Nat := 4983230072969 + 3 ^ 40 * 1305326 * 2
def baseEnd_1305326 : Nat := 670259648810865139721921

theorem tailTrace_1305326 : CollatzResearch.WordTrace tailWord_1305326 prefixEnd_1305326 670259648810865139721921 := by
  unfold tailWord_1305326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951143808629288597173979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31739433646022872518261221 5951143808629288597173979)
  ·
    refine ⟨8926715712943932895760969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5951143808629288597173979 8926715712943932895760969)
    ·
      refine ⟨6695036784707949671820727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8926715712943932895760969 6695036784707949671820727)
      ·
        refine ⟨10042555177061924507731091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695036784707949671820727 10042555177061924507731091)
        ·
          refine ⟨15063832765592886761596637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10042555177061924507731091 15063832765592886761596637)
          ·
            refine ⟨5648937287097332535598739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15063832765592886761596637 5648937287097332535598739)
            ·
              refine ⟨8473405930645998803398109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648937287097332535598739 8473405930645998803398109)
              ·
                refine ⟨3177527223992249551274291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8473405930645998803398109 3177527223992249551274291)
                ·
                  refine ⟨4766290835988374326911437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177527223992249551274291 4766290835988374326911437)
                  ·
                    refine ⟨1787359063495640372591789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4766290835988374326911437 1787359063495640372591789)
                    ·
                      refine ⟨670259648810865139721921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1787359063495640372591789 670259648810865139721921)
                      ·
                        rfl

theorem cell23_1305326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1305326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305326 prefixEnd_1305326 := by exact prefixLift 1305326
  have htrace : WordTrace (prefixWord ++ tailWord_1305326) baseStart_1305326 baseEnd_1305326 := by
    simpa [prefixWord, tailWord_1305326, baseEnd_1305326] using wordTrace_append hprefix tailTrace_1305326
  have hstable : (prefixWord ++ tailWord_1305326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305326).length < 2 ^ (prefixWord ++ tailWord_1305326).sum := by decide
  have hdescent : baseEnd_1305326 < baseStart_1305326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305336 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 3, 3, 2]
def baseStart_1305336 : Nat := 118140960795 + 1305336 * 2 ^ 59
def prefixEnd_1305336 : Nat := 4983230072969 + 3 ^ 40 * 1305336 * 2
def baseEnd_1305336 : Nat := 670264783617410100596875

theorem tailTrace_1305336 : CollatzResearch.WordTrace tailWord_1305336 prefixEnd_1305336 670264783617410100596875 := by
  unfold tailWord_1305336
  simp only [CollatzResearch.WordTrace]
  refine ⟨23804757599499040242627931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31739676799332053656837241 23804757599499040242627931)
  ·
    refine ⟨35707136399248560363941897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23804757599499040242627931 35707136399248560363941897)
    ·
      refine ⟨26780352299436420272956423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35707136399248560363941897 26780352299436420272956423)
      ·
        refine ⟨40170528449154630409434635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26780352299436420272956423 40170528449154630409434635)
        ·
          refine ⟨60255792673731945614151953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40170528449154630409434635 60255792673731945614151953)
          ·
            refine ⟨45191844505298959210613965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60255792673731945614151953 45191844505298959210613965)
            ·
              refine ⟨16946941689487109703980237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45191844505298959210613965 16946941689487109703980237)
              ·
                refine ⟨6355103133557666138992589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16946941689487109703980237 6355103133557666138992589)
                ·
                  refine ⟨2383163675084124802122221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6355103133557666138992589 2383163675084124802122221)
                  ·
                    refine ⟨893686378156546800795833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383163675084124802122221 893686378156546800795833)
                    ·
                      refine ⟨670264783617410100596875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 893686378156546800795833 670264783617410100596875)
                      ·
                        rfl

theorem cell23_1305336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_1305336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305336 prefixEnd_1305336 := by exact prefixLift 1305336
  have htrace : WordTrace (prefixWord ++ tailWord_1305336) baseStart_1305336 baseEnd_1305336 := by
    simpa [prefixWord, tailWord_1305336, baseEnd_1305336] using wordTrace_append hprefix tailTrace_1305336
  have hstable : (prefixWord ++ tailWord_1305336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305336).length < 2 ^ (prefixWord ++ tailWord_1305336).sum := by decide
  have hdescent : baseEnd_1305336 < baseStart_1305336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305369 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_1305369 : Nat := 118140960795 + 1305369 * 2 ^ 59
def prefixEnd_1305369 : Nat := 4983230072969 + 3 ^ 40 * 1305369 * 2
def baseEnd_1305369 : Nat := 670281728479008471484223

theorem tailTrace_1305369 : CollatzResearch.WordTrace tailWord_1305369 prefixEnd_1305369 670281728479008471484223 := by
  unfold tailWord_1305369
  simp only [CollatzResearch.WordTrace]
  refine ⟨47610718807878527121207161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31740479205252351414138107 47610718807878527121207161)
  ·
    refine ⟨35708039105908895340905371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47610718807878527121207161 35708039105908895340905371)
    ·
      refine ⟨53562058658863343011358057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35708039105908895340905371 53562058658863343011358057)
      ·
        refine ⟨40171543994147507258518543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53562058658863343011358057 40171543994147507258518543)
        ·
          refine ⟨60257315991221260887777815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40171543994147507258518543 60257315991221260887777815)
          ·
            refine ⟨90385973986831891331666723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60257315991221260887777815 90385973986831891331666723)
            ·
              refine ⟨135578960980247836997500085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90385973986831891331666723 135578960980247836997500085)
              ·
                refine ⟨12710527591898234718515633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135578960980247836997500085 12710527591898234718515633)
                ·
                  refine ⟨9532895693923676038886725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12710527591898234718515633 9532895693923676038886725)
                  ·
                    refine ⟨1787417942610689257291261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9532895693923676038886725 1787417942610689257291261)
                    ·
                      refine ⟨670281728479008471484223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1787417942610689257291261 670281728479008471484223)
                      ·
                        rfl

theorem cell23_1305369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_1305369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305369 prefixEnd_1305369 := by exact prefixLift 1305369
  have htrace : WordTrace (prefixWord ++ tailWord_1305369) baseStart_1305369 baseEnd_1305369 := by
    simpa [prefixWord, tailWord_1305369, baseEnd_1305369] using wordTrace_append hprefix tailTrace_1305369
  have hstable : (prefixWord ++ tailWord_1305369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305369).length < 2 ^ (prefixWord ++ tailWord_1305369).sum := by decide
  have hdescent : baseEnd_1305369 < baseStart_1305369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305456 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_1305456 : Nat := 118140960795 + 1305456 * 2 ^ 59
def prefixEnd_1305456 : Nat := 4983230072969 + 3 ^ 40 * 1305456 * 2
def baseEnd_1305456 : Nat := 670326401295949631096323

theorem tailTrace_1305456 : CollatzResearch.WordTrace tailWord_1305456 prefixEnd_1305456 670326401295949631096323 := by
  unfold tailWord_1305456
  simp only [CollatzResearch.WordTrace]
  refine ⟨23806945979281670489812111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31742594639042227319749481 23806945979281670489812111)
  ·
    refine ⟨35710418968922505734718167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23806945979281670489812111 35710418968922505734718167)
    ·
      refine ⟨53565628453383758602077251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35710418968922505734718167 53565628453383758602077251)
      ·
        refine ⟨80348442680075637903115877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53565628453383758602077251 80348442680075637903115877)
        ·
          refine ⟨15065333002514182106834227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80348442680075637903115877 15065333002514182106834227)
          ·
            refine ⟨22597999503771273160251341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065333002514182106834227 22597999503771273160251341)
            ·
              refine ⟨8474249813914227435094253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22597999503771273160251341 8474249813914227435094253)
              ·
                refine ⟨3177843680217835288160345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8474249813914227435094253 3177843680217835288160345)
                ·
                  refine ⟨2383382760163376466120259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177843680217835288160345 2383382760163376466120259)
                  ·
                    refine ⟨3575074140245064699180389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2383382760163376466120259 3575074140245064699180389)
                    ·
                      refine ⟨670326401295949631096323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3575074140245064699180389 670326401295949631096323)
                      ·
                        rfl

theorem cell23_1305456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_1305456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305456 prefixEnd_1305456 := by exact prefixLift 1305456
  have htrace : WordTrace (prefixWord ++ tailWord_1305456) baseStart_1305456 baseEnd_1305456 := by
    simpa [prefixWord, tailWord_1305456, baseEnd_1305456] using wordTrace_append hprefix tailTrace_1305456
  have hstable : (prefixWord ++ tailWord_1305456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305456).length < 2 ^ (prefixWord ++ tailWord_1305456).sum := by decide
  have hdescent : baseEnd_1305456 < baseStart_1305456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305476 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1305476 : Nat := 118140960795 + 1305476 * 2 ^ 59
def prefixEnd_1305476 : Nat := 4983230072969 + 3 ^ 40 * 1305476 * 2
def baseEnd_1305476 : Nat := 670336670909039552846231

theorem tailTrace_1305476 : CollatzResearch.WordTrace tailWord_1305476 prefixEnd_1305476 670336670909039552846231 := by
  unfold tailWord_1305476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23807310709245442197676141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31743080945660589596901521 23807310709245442197676141)
  ·
    refine ⟨8927741515967040824128553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23807310709245442197676141 8927741515967040824128553)
    ·
      refine ⟨6695806136975280618096415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8927741515967040824128553 6695806136975280618096415)
      ·
        refine ⟨10043709205462920927144623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695806136975280618096415 10043709205462920927144623)
        ·
          refine ⟨15065563808194381390716935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043709205462920927144623 15065563808194381390716935)
          ·
            refine ⟨22598345712291572086075403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065563808194381390716935 22598345712291572086075403)
            ·
              refine ⟨33897518568437358129113105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598345712291572086075403 33897518568437358129113105)
              ·
                refine ⟨25423138926328018596834829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33897518568437358129113105 25423138926328018596834829)
                ·
                  refine ⟨9533677097373006973813061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25423138926328018596834829 9533677097373006973813061)
                  ·
                    refine ⟨1787564455757438807589949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9533677097373006973813061 1787564455757438807589949)
                    ·
                      refine ⟨670336670909039552846231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1787564455757438807589949 670336670909039552846231)
                      ·
                        rfl

theorem cell23_1305476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1305476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305476 prefixEnd_1305476 := by exact prefixLift 1305476
  have htrace : WordTrace (prefixWord ++ tailWord_1305476) baseStart_1305476 baseEnd_1305476 := by
    simpa [prefixWord, tailWord_1305476, baseEnd_1305476] using wordTrace_append hprefix tailTrace_1305476
  have hstable : (prefixWord ++ tailWord_1305476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305476).length < 2 ^ (prefixWord ++ tailWord_1305476).sum := by decide
  have hdescent : baseEnd_1305476 < baseStart_1305476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305500 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1305500 : Nat := 118140960795 + 1305500 * 2 ^ 59
def prefixEnd_1305500 : Nat := 4983230072969 + 3 ^ 40 * 1305500 * 2
def baseEnd_1305500 : Nat := 223449664814915819648707

theorem tailTrace_1305500 : CollatzResearch.WordTrace tailWord_1305500 prefixEnd_1305500 223449664814915819648707 := by
  unfold tailWord_1305500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23807748385201968247112977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31743664513602624329483969 23807748385201968247112977)
  ·
    refine ⟨17855811288901476185334733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23807748385201968247112977 17855811288901476185334733)
    ·
      refine ⟨6695929233338053569500525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17855811288901476185334733 6695929233338053569500525)
      ·
        refine ⟨2510973462501770088562697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6695929233338053569500525 2510973462501770088562697)
        ·
          refine ⟨1883230096876327566422023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2510973462501770088562697 1883230096876327566422023)
          ·
            refine ⟨2824845145314491349633035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883230096876327566422023 2824845145314491349633035)
            ·
              refine ⟨4237267717971737024449553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824845145314491349633035 4237267717971737024449553)
              ·
                refine ⟨3177950788478802768337165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4237267717971737024449553 3177950788478802768337165)
                ·
                  refine ⟨1191731545679551038126437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3177950788478802768337165 1191731545679551038126437)
                  ·
                    refine ⟨223449664814915819648707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1191731545679551038126437 223449664814915819648707)
                    ·
                      rfl

theorem cell23_1305500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1305500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305500 prefixEnd_1305500 := by exact prefixLift 1305500
  have htrace : WordTrace (prefixWord ++ tailWord_1305500) baseStart_1305500 baseEnd_1305500 := by
    simpa [prefixWord, tailWord_1305500, baseEnd_1305500] using wordTrace_append hprefix tailTrace_1305500
  have hstable : (prefixWord ++ tailWord_1305500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305500).length < 2 ^ (prefixWord ++ tailWord_1305500).sum := by decide
  have hdescent : baseEnd_1305500 < baseStart_1305500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305583 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_1305583 : Nat := 118140960795 + 1305583 * 2 ^ 59
def prefixEnd_1305583 : Nat := 4983230072969 + 3 ^ 40 * 1305583 * 2
def baseEnd_1305583 : Nat := 670391613339070634208239

theorem tailTrace_1305583 : CollatzResearch.WordTrace tailWord_1305583 prefixEnd_1305583 670391613339070634208239 := by
  unfold tailWord_1305583
  simp only [CollatzResearch.WordTrace]
  refine ⟨47618524029103241669497403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31745682686068827779664935 47618524029103241669497403)
  ·
    refine ⟨71427786043654862504246105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47618524029103241669497403 71427786043654862504246105)
    ·
      refine ⟨53570839532741146878184579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71427786043654862504246105 53570839532741146878184579)
      ·
        refine ⟨80356259299111720317276869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53570839532741146878184579 80356259299111720317276869)
        ·
          refine ⟨15066798618583447559489413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80356259299111720317276869 15066798618583447559489413)
          ·
            refine ⟨2825024740984396417404265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15066798618583447559489413 2825024740984396417404265)
            ·
              refine ⟨2118768555738297313053199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825024740984396417404265 2118768555738297313053199)
              ·
                refine ⟨3178152833607445969579799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118768555738297313053199 3178152833607445969579799)
                ·
                  refine ⟨4767229250411168954369699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178152833607445969579799 4767229250411168954369699)
                  ·
                    refine ⟨7150843875616753431554549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4767229250411168954369699 7150843875616753431554549)
                    ·
                      refine ⟨670391613339070634208239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7150843875616753431554549 670391613339070634208239)
                      ·
                        rfl

theorem cell23_1305583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_1305583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305583 prefixEnd_1305583 := by exact prefixLift 1305583
  have htrace : WordTrace (prefixWord ++ tailWord_1305583) baseStart_1305583 baseEnd_1305583 := by
    simpa [prefixWord, tailWord_1305583, baseEnd_1305583] using wordTrace_append hprefix tailTrace_1305583
  have hstable : (prefixWord ++ tailWord_1305583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305583).length < 2 ^ (prefixWord ++ tailWord_1305583).sum := by decide
  have hdescent : baseEnd_1305583 < baseStart_1305583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305590 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1305590 : Nat := 118140960795 + 1305590 * 2 ^ 59
def prefixEnd_1305590 : Nat := 4983230072969 + 3 ^ 40 * 1305590 * 2
def baseEnd_1305590 : Nat := 223465069234550702273569

theorem tailTrace_1305590 : CollatzResearch.WordTrace tailWord_1305590 prefixEnd_1305590 223465069234550702273569 := by
  unfold tailWord_1305590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976173708754867616562639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31745852893385254576668149 2976173708754867616562639)
  ·
    refine ⟨4464260563132301424843959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976173708754867616562639 4464260563132301424843959)
    ·
      refine ⟨6696390844698452137265939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4464260563132301424843959 6696390844698452137265939)
      ·
        refine ⟨10044586267047678205898909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696390844698452137265939 10044586267047678205898909)
        ·
          refine ⟨3766719850142879327212091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10044586267047678205898909 3766719850142879327212091)
          ·
            refine ⟨5650079775214318990818137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766719850142879327212091 5650079775214318990818137)
            ·
              refine ⟨4237559831410739243113603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5650079775214318990818137 4237559831410739243113603)
              ·
                refine ⟨6356339747116108864670405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237559831410739243113603 6356339747116108864670405)
                ·
                  refine ⟨1191813702584270412125701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6356339747116108864670405 1191813702584270412125701)
                  ·
                    refine ⟨223465069234550702273569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1191813702584270412125701 223465069234550702273569)
                    ·
                      rfl

theorem cell23_1305590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1305590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305590 prefixEnd_1305590 := by exact prefixLift 1305590
  have htrace : WordTrace (prefixWord ++ tailWord_1305590) baseStart_1305590 baseEnd_1305590 := by
    simpa [prefixWord, tailWord_1305590, baseEnd_1305590] using wordTrace_append hprefix tailTrace_1305590
  have hstable : (prefixWord ++ tailWord_1305590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305590).length < 2 ^ (prefixWord ++ tailWord_1305590).sum := by decide
  have hdescent : baseEnd_1305590 < baseStart_1305590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305710 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_1305710 : Nat := 118140960795 + 1305710 * 2 ^ 59
def prefixEnd_1305710 : Nat := 4983230072969 + 3 ^ 40 * 1305710 * 2
def baseEnd_1305710 : Nat := 74495202820243515257795

theorem tailTrace_1305710 : CollatzResearch.WordTrace tailWord_1305710 prefixEnd_1305710 74495202820243515257795 := by
  unfold tailWord_1305710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952894512455392794921323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31748770733095428239580389 5952894512455392794921323)
  ·
    refine ⟨8929341768683089192381985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952894512455392794921323 8929341768683089192381985)
    ·
      refine ⟨6697006326512316894286489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8929341768683089192381985 6697006326512316894286489)
      ·
        refine ⟨5022754744884237670714867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6697006326512316894286489 5022754744884237670714867)
        ·
          refine ⟨7534132117326356506072301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022754744884237670714867 7534132117326356506072301)
          ·
            refine ⟨2825299543997383689777113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7534132117326356506072301 2825299543997383689777113)
            ·
              refine ⟨2118974657998037767332835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825299543997383689777113 2118974657998037767332835)
              ·
                refine ⟨3178461986997056650999253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118974657998037767332835 3178461986997056650999253)
                ·
                  refine ⟨74495202820243515257795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3178461986997056650999253 74495202820243515257795)
                  ·
                    rfl

theorem cell23_1305710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_1305710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305710 prefixEnd_1305710 := by exact prefixLift 1305710
  have htrace : WordTrace (prefixWord ++ tailWord_1305710) baseStart_1305710 baseEnd_1305710 := by
    simpa [prefixWord, tailWord_1305710, baseEnd_1305710] using wordTrace_append hprefix tailTrace_1305710
  have hstable : (prefixWord ++ tailWord_1305710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305710).length < 2 ^ (prefixWord ++ tailWord_1305710).sum := by decide
  have hdescent : baseEnd_1305710 < baseStart_1305710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305721 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 2, 2, 2]
def baseStart_1305721 : Nat := 118140960795 + 1305721 * 2 ^ 59
def prefixEnd_1305721 : Nat := 4983230072969 + 3 ^ 40 * 1305721 * 2
def baseEnd_1305721 : Nat := 670462473669391094282605

theorem tailTrace_1305721 : CollatzResearch.WordTrace tailWord_1305721 prefixEnd_1305721 670462473669391094282605 := by
  unfold tailWord_1305721
  simp only [CollatzResearch.WordTrace]
  refine ⟨47623557302603291238021017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31749038201735527492014011 47623557302603291238021017)
  ·
    refine ⟨35717667976952468428515763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47623557302603291238021017 35717667976952468428515763)
    ·
      refine ⟨53576501965428702642773645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35717667976952468428515763 53576501965428702642773645)
      ·
        refine ⟨20091188237035763491040117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53576501965428702642773645 20091188237035763491040117)
        ·
          refine ⟨1883548897222102827285011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20091188237035763491040117 1883548897222102827285011)
          ·
            refine ⟨2825323345833154240927517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883548897222102827285011 2825323345833154240927517)
            ·
              refine ⟨1059496254687432840347819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2825323345833154240927517 1059496254687432840347819)
              ·
                refine ⟨1589244382031149260521729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059496254687432840347819 1589244382031149260521729)
                ·
                  refine ⟨1191933286523361945391297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589244382031149260521729 1191933286523361945391297)
                  ·
                    refine ⟨893949964892521459043473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1191933286523361945391297 893949964892521459043473)
                    ·
                      refine ⟨670462473669391094282605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 893949964892521459043473 670462473669391094282605)
                      ·
                        rfl

theorem cell23_1305721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_1305721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305721 prefixEnd_1305721 := by exact prefixLift 1305721
  have htrace : WordTrace (prefixWord ++ tailWord_1305721) baseStart_1305721 baseEnd_1305721 := by
    simpa [prefixWord, tailWord_1305721, baseEnd_1305721] using wordTrace_append hprefix tailTrace_1305721
  have hstable : (prefixWord ++ tailWord_1305721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305721).length < 2 ^ (prefixWord ++ tailWord_1305721).sum := by decide
  have hdescent : baseEnd_1305721 < baseStart_1305721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305760 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1305760 : Nat := 118140960795 + 1305760 * 2 ^ 59
def prefixEnd_1305760 : Nat := 4983230072969 + 3 ^ 40 * 1305760 * 2
def baseEnd_1305760 : Nat := 670482499414916441694925

theorem tailTrace_1305760 : CollatzResearch.WordTrace tailWord_1305760 prefixEnd_1305760 670482499414916441694925 := by
  unfold tailWord_1305760
  simp only [CollatzResearch.WordTrace]
  refine ⟨23812489874731000449345367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31749986499641333932460489 23812489874731000449345367)
  ·
    refine ⟨35718734812096500674018051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23812489874731000449345367 35718734812096500674018051)
    ·
      refine ⟨53578102218144751011027077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35718734812096500674018051 53578102218144751011027077)
      ·
        refine ⟨10045894165902140814567577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53578102218144751011027077 10045894165902140814567577)
        ·
          refine ⟨7534420624426605610925683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10045894165902140814567577 7534420624426605610925683)
          ·
            refine ⟨11301630936639908416388525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534420624426605610925683 11301630936639908416388525)
            ·
              refine ⟨4238111601239965656145697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11301630936639908416388525 4238111601239965656145697)
              ·
                refine ⟨3178583700929974242109273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4238111601239965656145697 3178583700929974242109273)
                ·
                  refine ⟨2383937775697480681581955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178583700929974242109273 2383937775697480681581955)
                  ·
                    refine ⟨3575906663546221022372933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2383937775697480681581955 3575906663546221022372933)
                    ·
                      refine ⟨670482499414916441694925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3575906663546221022372933 670482499414916441694925)
                      ·
                        rfl

theorem cell23_1305760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1305760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305760 prefixEnd_1305760 := by exact prefixLift 1305760
  have htrace : WordTrace (prefixWord ++ tailWord_1305760) baseStart_1305760 baseEnd_1305760 := by
    simpa [prefixWord, tailWord_1305760, baseEnd_1305760] using wordTrace_append hprefix tailTrace_1305760
  have hstable : (prefixWord ++ tailWord_1305760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305760).length < 2 ^ (prefixWord ++ tailWord_1305760).sum := by decide
  have hdescent : baseEnd_1305760 < baseStart_1305760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305821 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1305821 : Nat := 118140960795 + 1305821 * 2 ^ 59
def prefixEnd_1305821 : Nat := 4983230072969 + 3 ^ 40 * 1305821 * 2
def baseEnd_1305821 : Nat := 223504607244946901010715

theorem tailTrace_1305821 : CollatzResearch.WordTrace tailWord_1305821 prefixEnd_1305821 223504607244946901010715 := by
  unfold tailWord_1305821
  simp only [CollatzResearch.WordTrace]
  refine ⟨47627204602241008316661317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31751469734827338877774211 47627204602241008316661317)
  ·
    refine ⟨8930100862920189059373997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47627204602241008316661317 8930100862920189059373997)
    ·
      refine ⟨3348787823595070897265249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8930100862920189059373997 3348787823595070897265249)
      ·
        refine ⟨2511590867696303172948937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3348787823595070897265249 2511590867696303172948937)
        ·
          refine ⟨1883693150772227379711703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511590867696303172948937 1883693150772227379711703)
          ·
            refine ⟨2825539726158341069567555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883693150772227379711703 2825539726158341069567555)
            ·
              refine ⟨4238309589237511604351333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825539726158341069567555 4238309589237511604351333)
              ·
                refine ⟨794683047982033425815875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4238309589237511604351333 794683047982033425815875)
                ·
                  refine ⟨1192024571973050138723813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794683047982033425815875 1192024571973050138723813)
                  ·
                    refine ⟨223504607244946901010715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1192024571973050138723813 223504607244946901010715)
                    ·
                      rfl

theorem cell23_1305821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1305821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305821 prefixEnd_1305821 := by exact prefixLift 1305821
  have htrace : WordTrace (prefixWord ++ tailWord_1305821) baseStart_1305821 baseEnd_1305821 := by
    simpa [prefixWord, tailWord_1305821, baseEnd_1305821] using wordTrace_append hprefix tailTrace_1305821
  have hstable : (prefixWord ++ tailWord_1305821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305821).length < 2 ^ (prefixWord ++ tailWord_1305821).sum := by decide
  have hdescent : baseEnd_1305821 < baseStart_1305821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305833 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 4]
def baseStart_1305833 : Nat := 118140960795 + 1305833 * 2 ^ 59
def prefixEnd_1305833 : Nat := 4983230072969 + 3 ^ 40 * 1305833 * 2
def baseEnd_1305833 : Nat := 670519983502694656082089

theorem tailTrace_1305833 : CollatzResearch.WordTrace tailWord_1305833 prefixEnd_1305833 670519983502694656082089 := by
  unfold tailWord_1305833
  simp only [CollatzResearch.WordTrace]
  refine ⟨47627642278197534366098153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31751761518798356244065435 47627642278197534366098153)
  ·
    refine ⟨35720731708648150774573615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47627642278197534366098153 35720731708648150774573615)
    ·
      refine ⟨53581097562972226161860423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35720731708648150774573615 53581097562972226161860423)
      ·
        refine ⟨80371646344458339242790635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53581097562972226161860423 80371646344458339242790635)
        ·
          refine ⟨120557469516687508864185953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80371646344458339242790635 120557469516687508864185953)
          ·
            refine ⟨90418102137515631648139465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120557469516687508864185953 90418102137515631648139465)
            ·
              refine ⟨67813576603136723736104599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90418102137515631648139465 67813576603136723736104599)
              ·
                refine ⟨101720364904705085604156899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67813576603136723736104599 101720364904705085604156899)
                ·
                  refine ⟨152580547357057628406235349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101720364904705085604156899 152580547357057628406235349)
                  ·
                    refine ⟨3576106578681038165771141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 152580547357057628406235349 3576106578681038165771141)
                    ·
                      refine ⟨670519983502694656082089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3576106578681038165771141 670519983502694656082089)
                      ·
                        rfl

theorem cell23_1305833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_1305833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305833 prefixEnd_1305833 := by exact prefixLift 1305833
  have htrace : WordTrace (prefixWord ++ tailWord_1305833) baseStart_1305833 baseEnd_1305833 := by
    simpa [prefixWord, tailWord_1305833, baseEnd_1305833] using wordTrace_append hprefix tailTrace_1305833
  have hstable : (prefixWord ++ tailWord_1305833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305833).length < 2 ^ (prefixWord ++ tailWord_1305833).sum := by decide
  have hdescent : baseEnd_1305833 < baseStart_1305833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305850 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_1305850 : Nat := 118140960795 + 1305850 * 2 ^ 59
def prefixEnd_1305850 : Nat := 4983230072969 + 3 ^ 40 * 1305850 * 2
def baseEnd_1305850 : Nat := 670528712673821089569511

theorem tailTrace_1305850 : CollatzResearch.WordTrace tailWord_1305850 prefixEnd_1305850 670528712673821089569511 := by
  unfold tailWord_1305850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907065579783986567366751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31752174879423964179644669 11907065579783986567366751)
  ·
    refine ⟨17860598369675979851050127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11907065579783986567366751 17860598369675979851050127)
    ·
      refine ⟨26790897554513969776575191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17860598369675979851050127 26790897554513969776575191)
      ·
        refine ⟨40186346331770954664862787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26790897554513969776575191 40186346331770954664862787)
        ·
          refine ⟨60279519497656431997294181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40186346331770954664862787 60279519497656431997294181)
          ·
            refine ⟨11302409905810580999492659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60279519497656431997294181 11302409905810580999492659)
            ·
              refine ⟨16953614858715871499238989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11302409905810580999492659 16953614858715871499238989)
              ·
                refine ⟨6357605572018451812214621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16953614858715871499238989 6357605572018451812214621)
                ·
                  refine ⟨2384102089506919429580483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6357605572018451812214621 2384102089506919429580483)
                  ·
                    refine ⟨3576153134260379144370725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384102089506919429580483 3576153134260379144370725)
                    ·
                      refine ⟨670528712673821089569511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3576153134260379144370725 670528712673821089569511)
                      ·
                        rfl

theorem cell23_1305850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_1305850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305850 prefixEnd_1305850 := by exact prefixLift 1305850
  have htrace : WordTrace (prefixWord ++ tailWord_1305850) baseStart_1305850 baseEnd_1305850 := by
    simpa [prefixWord, tailWord_1305850, baseEnd_1305850] using wordTrace_append hprefix tailTrace_1305850
  have hstable : (prefixWord ++ tailWord_1305850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305850).length < 2 ^ (prefixWord ++ tailWord_1305850).sum := by decide
  have hdescent : baseEnd_1305850 < baseStart_1305850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305854 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_1305854 : Nat := 118140960795 + 1305854 * 2 ^ 59
def prefixEnd_1305854 : Nat := 4983230072969 + 3 ^ 40 * 1305854 * 2
def baseEnd_1305854 : Nat := 670530766596439073919493

theorem tailTrace_1305854 : CollatzResearch.WordTrace tailWord_1305854 prefixEnd_1305854 670530766596439073919493 := by
  unfold tailWord_1305854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5953551026390181869076577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31752272140747636635075077 5953551026390181869076577)
  ·
    refine ⟨4465163269792636401807433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5953551026390181869076577 4465163269792636401807433)
    ·
      refine ⟨3348872452344477301355575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4465163269792636401807433 3348872452344477301355575)
      ·
        refine ⟨5023308678516715952033363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3348872452344477301355575 5023308678516715952033363)
        ·
          refine ⟨7534963017775073928050045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5023308678516715952033363 7534963017775073928050045)
          ·
            refine ⟨2825611131665652723018767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7534963017775073928050045 2825611131665652723018767)
            ·
              refine ⟨4238416697498479084528151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825611131665652723018767 4238416697498479084528151)
              ·
                refine ⟨6357625046247718626792227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238416697498479084528151 6357625046247718626792227)
                ·
                  refine ⟨9536437569371577940188341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357625046247718626792227 9536437569371577940188341)
                  ·
                    refine ⟨894041022128585431892657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9536437569371577940188341 894041022128585431892657)
                    ·
                      refine ⟨670530766596439073919493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894041022128585431892657 670530766596439073919493)
                      ·
                        rfl

theorem cell23_1305854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_1305854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305854 prefixEnd_1305854 := by exact prefixLift 1305854
  have htrace : WordTrace (prefixWord ++ tailWord_1305854) baseStart_1305854 baseEnd_1305854 := by
    simpa [prefixWord, tailWord_1305854, baseEnd_1305854] using wordTrace_append hprefix tailTrace_1305854
  have hstable : (prefixWord ++ tailWord_1305854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305854).length < 2 ^ (prefixWord ++ tailWord_1305854).sum := by decide
  have hdescent : baseEnd_1305854 < baseStart_1305854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305867 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 4]
def baseStart_1305867 : Nat := 118140960795 + 1305867 * 2 ^ 59
def prefixEnd_1305867 : Nat := 4983230072969 + 3 ^ 40 * 1305867 * 2
def baseEnd_1305867 : Nat := 670537441844947523056933

theorem tailTrace_1305867 : CollatzResearch.WordTrace tailWord_1305867 prefixEnd_1305867 670537441844947523056933 := by
  unfold tailWord_1305867
  simp only [CollatzResearch.WordTrace]
  refine ⟨47628882360074358172835855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31752588240049572115223903 47628882360074358172835855)
  ·
    refine ⟨71443323540111537259253783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47628882360074358172835855 71443323540111537259253783)
    ·
      refine ⟨107164985310167305888880675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71443323540111537259253783 107164985310167305888880675)
      ·
        refine ⟨160747477965250958833321013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107164985310167305888880675 160747477965250958833321013)
        ·
          refine ⟨15070076059242277390623845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160747477965250958833321013 15070076059242277390623845)
          ·
            refine ⟨2825639261107927010741971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15070076059242277390623845 2825639261107927010741971)
            ·
              refine ⟨4238458891661890516112957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825639261107927010741971 4238458891661890516112957)
              ·
                refine ⟨1589422084373208943542359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4238458891661890516112957 1589422084373208943542359)
                ·
                  refine ⟨2384133126559813415313539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589422084373208943542359 2384133126559813415313539)
                  ·
                    refine ⟨3576199689839720122970309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384133126559813415313539 3576199689839720122970309)
                    ·
                      refine ⟨670537441844947523056933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3576199689839720122970309 670537441844947523056933)
                      ·
                        rfl

theorem cell23_1305867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 1, 4].length) (baseStart_1305867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305867 prefixEnd_1305867 := by exact prefixLift 1305867
  have htrace : WordTrace (prefixWord ++ tailWord_1305867) baseStart_1305867 baseEnd_1305867 := by
    simpa [prefixWord, tailWord_1305867, baseEnd_1305867] using wordTrace_append hprefix tailTrace_1305867
  have hstable : (prefixWord ++ tailWord_1305867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305867).length < 2 ^ (prefixWord ++ tailWord_1305867).sum := by decide
  have hdescent : baseEnd_1305867 < baseStart_1305867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305873 : List Nat := [1, 2, 2, 1, 1, 4, 12]
def baseStart_1305873 : Nat := 118140960795 + 1305873 * 2 ^ 59
def prefixEnd_1305873 : Nat := 4983230072969 + 3 ^ 40 * 1305873 * 2
def baseEnd_1305873 : Nat := 8278278058381166661505

theorem tailTrace_1305873 : CollatzResearch.WordTrace tailWord_1305873 prefixEnd_1305873 8278278058381166661505 := by
  unfold tailWord_1305873
  simp only [CollatzResearch.WordTrace]
  refine ⟨47629101198052621197554273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31752734132035080798369515 47629101198052621197554273)
  ·
    refine ⟨35721825898539465898165705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47629101198052621197554273 35721825898539465898165705)
    ·
      refine ⟨26791369423904599423624279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35721825898539465898165705 26791369423904599423624279)
      ·
        refine ⟨40187054135856899135436419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26791369423904599423624279 40187054135856899135436419)
        ·
          refine ⟨60280581203785348703154629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40187054135856899135436419 60280581203785348703154629)
          ·
            refine ⟨11302608975709752881841493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60280581203785348703154629 11302608975709752881841493)
            ·
              refine ⟨8278278058381166661505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 11302608975709752881841493 8278278058381166661505)
              ·
                rfl

theorem cell23_1305873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 12].length) (baseStart_1305873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305873 prefixEnd_1305873 := by exact prefixLift 1305873
  have htrace : WordTrace (prefixWord ++ tailWord_1305873) baseStart_1305873 baseEnd_1305873 := by
    simpa [prefixWord, tailWord_1305873, baseEnd_1305873] using wordTrace_append hprefix tailTrace_1305873
  have hstable : (prefixWord ++ tailWord_1305873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305873).length < 2 ^ (prefixWord ++ tailWord_1305873).sum := by decide
  have hdescent : baseEnd_1305873 < baseStart_1305873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305883 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_1305883 : Nat := 118140960795 + 1305883 * 2 ^ 59
def prefixEnd_1305883 : Nat := 4983230072969 + 3 ^ 40 * 1305883 * 2
def baseEnd_1305883 : Nat := 670545657535419460456859

theorem tailTrace_1305883 : CollatzResearch.WordTrace tailWord_1305883 prefixEnd_1305883 670545657535419460456859 := by
  unfold tailWord_1305883
  simp only [CollatzResearch.WordTrace]
  refine ⟨47629465928016392905418303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31752977285344261936945535 47629465928016392905418303)
  ·
    refine ⟨71444198892024589358127455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47629465928016392905418303 71444198892024589358127455)
    ·
      refine ⟨107166298338036884037191183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71444198892024589358127455 107166298338036884037191183)
      ·
        refine ⟨160749447507055326055786775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107166298338036884037191183 160749447507055326055786775)
        ·
          refine ⟨241124171260582989083680163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160749447507055326055786775 241124171260582989083680163)
          ·
            refine ⟨361686256890874483625520245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241124171260582989083680163 361686256890874483625520245)
            ·
              refine ⟨33908086583519482839892523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361686256890874483625520245 33908086583519482839892523)
              ·
                refine ⟨50862129875279224259838785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33908086583519482839892523 50862129875279224259838785)
                ·
                  refine ⟨38146597406459418194879089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50862129875279224259838785 38146597406459418194879089)
                  ·
                    refine ⟨28609948054844563646159317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38146597406459418194879089 28609948054844563646159317)
                    ·
                      refine ⟨670545657535419460456859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28609948054844563646159317 670545657535419460456859)
                      ·
                        rfl

theorem cell23_1305883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_1305883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305883 prefixEnd_1305883 := by exact prefixLift 1305883
  have htrace : WordTrace (prefixWord ++ tailWord_1305883) baseStart_1305883 baseEnd_1305883 := by
    simpa [prefixWord, tailWord_1305883, baseEnd_1305883] using wordTrace_append hprefix tailTrace_1305883
  have hstable : (prefixWord ++ tailWord_1305883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305883).length < 2 ^ (prefixWord ++ tailWord_1305883).sum := by decide
  have hdescent : baseEnd_1305883 < baseStart_1305883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305884 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_1305884 : Nat := 118140960795 + 1305884 * 2 ^ 59
def prefixEnd_1305884 : Nat := 4983230072969 + 3 ^ 40 * 1305884 * 2
def baseEnd_1305884 : Nat := 670546171016073956544355

theorem tailTrace_1305884 : CollatzResearch.WordTrace tailWord_1305884 prefixEnd_1305884 670546171016073956544355 := by
  unfold tailWord_1305884
  simp only [CollatzResearch.WordTrace]
  refine ⟨23814751200506385038102353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31753001600675180050803137 23814751200506385038102353)
  ·
    refine ⟨17861063400379788778576765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23814751200506385038102353 17861063400379788778576765)
    ·
      refine ⟨6697898775142420791966287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17861063400379788778576765 6697898775142420791966287)
      ·
        refine ⟨10046848162713631187949431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697898775142420791966287 10046848162713631187949431)
        ·
          refine ⟨15070272244070446781924147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046848162713631187949431 15070272244070446781924147)
          ·
            refine ⟨22605408366105670172886221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15070272244070446781924147 22605408366105670172886221)
            ·
              refine ⟨8477028137289626314832333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22605408366105670172886221 8477028137289626314832333)
              ·
                refine ⟨3178885551483609868062125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8477028137289626314832333 3178885551483609868062125)
                ·
                  refine ⟨1192082081806353700523297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3178885551483609868062125 1192082081806353700523297)
                  ·
                    refine ⟨894061561354765275392473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1192082081806353700523297 894061561354765275392473)
                    ·
                      refine ⟨670546171016073956544355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894061561354765275392473 670546171016073956544355)
                      ·
                        rfl

theorem cell23_1305884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_1305884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305884 prefixEnd_1305884 := by exact prefixLift 1305884
  have htrace : WordTrace (prefixWord ++ tailWord_1305884) baseStart_1305884 baseEnd_1305884 := by
    simpa [prefixWord, tailWord_1305884, baseEnd_1305884] using wordTrace_append hprefix tailTrace_1305884
  have hstable : (prefixWord ++ tailWord_1305884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305884).length < 2 ^ (prefixWord ++ tailWord_1305884).sum := by decide
  have hdescent : baseEnd_1305884 < baseStart_1305884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305887 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_1305887 : Nat := 118140960795 + 1305887 * 2 ^ 59
def prefixEnd_1305887 : Nat := 4983230072969 + 3 ^ 40 * 1305887 * 2
def baseEnd_1305887 : Nat := 670547711458037444806841

theorem tailTrace_1305887 : CollatzResearch.WordTrace tailWord_1305887 prefixEnd_1305887 670547711458037444806841 := by
  unfold tailWord_1305887
  simp only [CollatzResearch.WordTrace]
  refine ⟨47629611820001901588563915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31753074546667934392375943 47629611820001901588563915)
  ·
    refine ⟨71444417730002852382845873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47629611820001901588563915 71444417730002852382845873)
    ·
      refine ⟨53583313297502139287134405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71444417730002852382845873 53583313297502139287134405)
      ·
        refine ⟨10046871243281651116337701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53583313297502139287134405 10046871243281651116337701)
        ·
          refine ⟨1883788358115309584313319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10046871243281651116337701 1883788358115309584313319)
          ·
            refine ⟨2825682537172964376469979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883788358115309584313319 2825682537172964376469979)
            ·
              refine ⟨4238523805759446564704969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825682537172964376469979 4238523805759446564704969)
              ·
                refine ⟨3178892854319584923528727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4238523805759446564704969 3178892854319584923528727)
                ·
                  refine ⟨4768339281479377385293091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178892854319584923528727 4768339281479377385293091)
                  ·
                    refine ⟨7152508922219066077939637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4768339281479377385293091 7152508922219066077939637)
                    ·
                      refine ⟨670547711458037444806841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7152508922219066077939637 670547711458037444806841)
                      ·
                        rfl

theorem cell23_1305887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_1305887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305887 prefixEnd_1305887 := by exact prefixLift 1305887
  have htrace : WordTrace (prefixWord ++ tailWord_1305887) baseStart_1305887 baseEnd_1305887 := by
    simpa [prefixWord, tailWord_1305887, baseEnd_1305887] using wordTrace_append hprefix tailTrace_1305887
  have hstable : (prefixWord ++ tailWord_1305887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305887).length < 2 ^ (prefixWord ++ tailWord_1305887).sum := by decide
  have hdescent : baseEnd_1305887 < baseStart_1305887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305901 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1305901 : Nat := 118140960795 + 1305901 * 2 ^ 59
def prefixEnd_1305901 : Nat := 4983230072969 + 3 ^ 40 * 1305901 * 2
def baseEnd_1305901 : Nat := 670554900187200390031777

theorem tailTrace_1305901 : CollatzResearch.WordTrace tailWord_1305901 prefixEnd_1305901 670554900187200390031777 := by
  unfold tailWord_1305901
  simp only [CollatzResearch.WordTrace]
  refine ⟨47630122441951181979573557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31753414961300787986382371 47630122441951181979573557)
  ·
    refine ⟨4465323978932923310585021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47630122441951181979573557 4465323978932923310585021)
    ·
      refine ⟨1674496492099846241469383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4465323978932923310585021 1674496492099846241469383)
      ·
        refine ⟨2511744738149769362204075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674496492099846241469383 2511744738149769362204075)
        ·
          refine ⟨3767617107224654043306113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511744738149769362204075 3767617107224654043306113)
          ·
            refine ⟨2825712830418490532479585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767617107224654043306113 2825712830418490532479585)
            ·
              refine ⟨2119284622813867899359689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825712830418490532479585 2119284622813867899359689)
              ·
                refine ⟨1589463467110400924519767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2119284622813867899359689 1589463467110400924519767)
                ·
                  refine ⟨2384195200665601386779651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589463467110400924519767 2384195200665601386779651)
                  ·
                    refine ⟨3576292800998402080169477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384195200665601386779651 3576292800998402080169477)
                    ·
                      refine ⟨670554900187200390031777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3576292800998402080169477 670554900187200390031777)
                      ·
                        rfl

theorem cell23_1305901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1305901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305901 prefixEnd_1305901 := by exact prefixLift 1305901
  have htrace : WordTrace (prefixWord ++ tailWord_1305901) baseStart_1305901 baseEnd_1305901 := by
    simpa [prefixWord, tailWord_1305901, baseEnd_1305901] using wordTrace_append hprefix tailTrace_1305901
  have hstable : (prefixWord ++ tailWord_1305901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305901).length < 2 ^ (prefixWord ++ tailWord_1305901).sum := by decide
  have hdescent : baseEnd_1305901 < baseStart_1305901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305907 : List Nat := [1, 1, 1, 2, 5, 4, 2, 7]
def baseStart_1305907 : Nat := 118140960795 + 1305907 * 2 ^ 59
def prefixEnd_1305907 : Nat := 4983230072969 + 3 ^ 40 * 1305907 * 2
def baseEnd_1305907 : Nat := 24835480780412124687287

theorem tailTrace_1305907 : CollatzResearch.WordTrace tailWord_1305907 prefixEnd_1305907 24835480780412124687287 := by
  unfold tailWord_1305907
  simp only [CollatzResearch.WordTrace]
  refine ⟨47630341279929445004291975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31753560853286296669527983 47630341279929445004291975)
  ·
    refine ⟨71445511919894167506437963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47630341279929445004291975 71445511919894167506437963)
    ·
      refine ⟨107168267879841251259656945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71445511919894167506437963 107168267879841251259656945)
      ·
        refine ⟨80376200909880938444742709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107168267879841251259656945 80376200909880938444742709)
        ·
          refine ⟨7535268835301337979194629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80376200909880938444742709 7535268835301337979194629)
          ·
            refine ⟨1412862906619000871098993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7535268835301337979194629 1412862906619000871098993)
            ·
              refine ⟨1059647179964250653324245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412862906619000871098993 1059647179964250653324245)
              ·
                refine ⟨24835480780412124687287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1059647179964250653324245 24835480780412124687287)
                ·
                  rfl

theorem cell23_1305907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 7].length) (baseStart_1305907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305907 prefixEnd_1305907 := by exact prefixLift 1305907
  have htrace : WordTrace (prefixWord ++ tailWord_1305907) baseStart_1305907 baseEnd_1305907 := by
    simpa [prefixWord, tailWord_1305907, baseEnd_1305907] using wordTrace_append hprefix tailTrace_1305907
  have hstable : (prefixWord ++ tailWord_1305907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305907).length < 2 ^ (prefixWord ++ tailWord_1305907).sum := by decide
  have hdescent : baseEnd_1305907 < baseStart_1305907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305934 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_1305934 : Nat := 118140960795 + 1305934 * 2 ^ 59
def prefixEnd_1305934 : Nat := 4983230072969 + 3 ^ 40 * 1305934 * 2
def baseEnd_1305934 : Nat := 670571845048798760919125

theorem tailTrace_1305934 : CollatzResearch.WordTrace tailWord_1305934 prefixEnd_1305934 670571845048798760919125 := by
  unfold tailWord_1305934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5953915756353953576940607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31754217367221085743683237 5953915756353953576940607)
  ·
    refine ⟨8930873634530930365410911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5953915756353953576940607 8930873634530930365410911)
    ·
      refine ⟨13396310451796395548116367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8930873634530930365410911 13396310451796395548116367)
      ·
        refine ⟨20094465677694593322174551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13396310451796395548116367 20094465677694593322174551)
        ·
          refine ⟨30141698516541889983261827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20094465677694593322174551 30141698516541889983261827)
          ·
            refine ⟨45212547774812834974892741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30141698516541889983261827 45212547774812834974892741)
            ·
              refine ⟨8477352707777406557792389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45212547774812834974892741 8477352707777406557792389)
              ·
                refine ⟨1589503632708263729586073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8477352707777406557792389 1589503632708263729586073)
                ·
                  refine ⟨1192127724531197797189555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589503632708263729586073 1192127724531197797189555)
                  ·
                    refine ⟨1788191586796796695784333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1192127724531197797189555 1788191586796796695784333)
                    ·
                      refine ⟨670571845048798760919125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1788191586796796695784333 670571845048798760919125)
                      ·
                        rfl

theorem cell23_1305934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_1305934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305934 prefixEnd_1305934 := by exact prefixLift 1305934
  have htrace : WordTrace (prefixWord ++ tailWord_1305934) baseStart_1305934 baseEnd_1305934 := by
    simpa [prefixWord, tailWord_1305934, baseEnd_1305934] using wordTrace_append hprefix tailTrace_1305934
  have hstable : (prefixWord ++ tailWord_1305934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305934).length < 2 ^ (prefixWord ++ tailWord_1305934).sum := by decide
  have hdescent : baseEnd_1305934 < baseStart_1305934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305991 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_1305991 : Nat := 118140960795 + 1305991 * 2 ^ 59
def prefixEnd_1305991 : Nat := 4983230072969 + 3 ^ 40 * 1305991 * 2
def baseEnd_1305991 : Nat := 670601113446105037906363

theorem tailTrace_1305991 : CollatzResearch.WordTrace tailWord_1305991 prefixEnd_1305991 670601113446105037906363 := by
  unfold tailWord_1305991
  simp only [CollatzResearch.WordTrace]
  refine ⟨47633405011625127350349827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31755603341083418233566551 47633405011625127350349827)
  ·
    refine ⟨71450107517437691025524741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47633405011625127350349827 71450107517437691025524741)
    ·
      refine ⟨13396895159519567067285889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71450107517437691025524741 13396895159519567067285889)
      ·
        refine ⟨10047671369639675300464417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13396895159519567067285889 10047671369639675300464417)
        ·
          refine ⟨7535753527229756475348313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10047671369639675300464417 7535753527229756475348313)
          ·
            refine ⟨5651815145422317356511235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7535753527229756475348313 5651815145422317356511235)
            ·
              refine ⟨8477722718133476034766853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651815145422317356511235 8477722718133476034766853)
              ·
                refine ⟨1589573009650026756518785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8477722718133476034766853 1589573009650026756518785)
                ·
                  refine ⟨1192179757237520067389089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589573009650026756518785 1192179757237520067389089)
                  ·
                    refine ⟨894134817928140050541817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1192179757237520067389089 894134817928140050541817)
                    ·
                      refine ⟨670601113446105037906363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894134817928140050541817 670601113446105037906363)
                      ·
                        rfl

theorem cell23_1305991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_1305991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1305991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1305991 prefixEnd_1305991 := by exact prefixLift 1305991
  have htrace : WordTrace (prefixWord ++ tailWord_1305991) baseStart_1305991 baseEnd_1305991 := by
    simpa [prefixWord, tailWord_1305991, baseEnd_1305991] using wordTrace_append hprefix tailTrace_1305991
  have hstable : (prefixWord ++ tailWord_1305991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305991).length < 2 ^ (prefixWord ++ tailWord_1305991).sum := by decide
  have hdescent : baseEnd_1305991 < baseStart_1305991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306004 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1306004 : Nat := 118140960795 + 1306004 * 2 ^ 59
def prefixEnd_1306004 : Nat := 4983230072969 + 3 ^ 40 * 1306004 * 2
def baseEnd_1306004 : Nat := 670607788694613487043803

theorem tailTrace_1306004 : CollatzResearch.WordTrace tailWord_1306004 prefixEnd_1306004 670607788694613487043803 := by
  unfold tailWord_1306004
  simp only [CollatzResearch.WordTrace]
  refine ⟨23816939580289015285286533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31755919440385353713715377 23816939580289015285286533)
  ·
    refine ⟨4465676171304190365991225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23816939580289015285286533 4465676171304190365991225)
    ·
      refine ⟨3349257128478142774493419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4465676171304190365991225 3349257128478142774493419)
      ·
        refine ⟨5023885692717214161740129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349257128478142774493419 5023885692717214161740129)
        ·
          refine ⟨3767914269537910621305097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5023885692717214161740129 3767914269537910621305097)
          ·
            refine ⟨2825935702153432965978823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767914269537910621305097 2825935702153432965978823)
            ·
              refine ⟨4238903553230149448968235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825935702153432965978823 4238903553230149448968235)
              ·
                refine ⟨6358355329845224173452353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238903553230149448968235 6358355329845224173452353)
                ·
                  refine ⟨4768766497383918130089265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6358355329845224173452353 4768766497383918130089265)
                  ·
                    refine ⟨3576574873037938597566949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4768766497383918130089265 3576574873037938597566949)
                    ·
                      refine ⟨670607788694613487043803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3576574873037938597566949 670607788694613487043803)
                      ·
                        rfl

theorem cell23_1306004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1306004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306004 prefixEnd_1306004 := by exact prefixLift 1306004
  have htrace : WordTrace (prefixWord ++ tailWord_1306004) baseStart_1306004 baseEnd_1306004 := by
    simpa [prefixWord, tailWord_1306004, baseEnd_1306004] using wordTrace_append hprefix tailTrace_1306004
  have hstable : (prefixWord ++ tailWord_1306004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306004).length < 2 ^ (prefixWord ++ tailWord_1306004).sum := by decide
  have hdescent : baseEnd_1306004 < baseStart_1306004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306047 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_1306047 : Nat := 118140960795 + 1306047 * 2 ^ 59
def prefixEnd_1306047 : Nat := 4983230072969 + 3 ^ 40 * 1306047 * 2
def baseEnd_1306047 : Nat := 670629868362756818806105

theorem tailTrace_1306047 : CollatzResearch.WordTrace tailWord_1306047 prefixEnd_1306047 670629868362756818806105 := by
  unfold tailWord_1306047
  simp only [CollatzResearch.WordTrace]
  refine ⟨47635447499422248914388395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31756964999614832609592263 47635447499422248914388395)
  ·
    refine ⟨71453171249133373371582593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47635447499422248914388395 71453171249133373371582593)
    ·
      refine ⟨53589878436850030028686945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71453171249133373371582593 53589878436850030028686945)
      ·
        refine ⟨40192408827637522521515209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53589878436850030028686945 40192408827637522521515209)
        ·
          refine ⟨30144306620728141891136407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40192408827637522521515209 30144306620728141891136407)
          ·
            refine ⟨45216459931092212836704611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30144306620728141891136407 45216459931092212836704611)
            ·
              refine ⟨67824689896638319255056917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45216459931092212836704611 67824689896638319255056917)
              ·
                refine ⟨3179282338904921215080793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67824689896638319255056917 3179282338904921215080793)
                ·
                  refine ⟨2384461754178690911310595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179282338904921215080793 2384461754178690911310595)
                  ·
                    refine ⟨3576692631268036366965893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384461754178690911310595 3576692631268036366965893)
                    ·
                      refine ⟨670629868362756818806105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3576692631268036366965893 670629868362756818806105)
                      ·
                        rfl

theorem cell23_1306047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_1306047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306047 prefixEnd_1306047 := by exact prefixLift 1306047
  have htrace : WordTrace (prefixWord ++ tailWord_1306047) baseStart_1306047 baseEnd_1306047 := by
    simpa [prefixWord, tailWord_1306047, baseEnd_1306047] using wordTrace_append hprefix tailTrace_1306047
  have hstable : (prefixWord ++ tailWord_1306047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306047).length < 2 ^ (prefixWord ++ tailWord_1306047).sum := by decide
  have hdescent : baseEnd_1306047 < baseStart_1306047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306074 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_1306074 : Nat := 118140960795 + 1306074 * 2 ^ 59
def prefixEnd_1306074 : Nat := 4983230072969 + 3 ^ 40 * 1306074 * 2
def baseEnd_1306074 : Nat := 223547910780142737722827

theorem tailTrace_1306074 : CollatzResearch.WordTrace tailWord_1306074 prefixEnd_1306074 223547910780142737722827 := by
  unfold tailWord_1306074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11909108067581108131405319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31757621513549621683747517 11909108067581108131405319)
  ·
    refine ⟨17863662101371662197107979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11909108067581108131405319 17863662101371662197107979)
    ·
      refine ⟨26795493152057493295661969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863662101371662197107979 26795493152057493295661969)
      ·
        refine ⟨20096619864043119971746477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26795493152057493295661969 20096619864043119971746477)
        ·
          refine ⟨7536232449016169989404929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20096619864043119971746477 7536232449016169989404929)
          ·
            refine ⟨5652174336762127492053697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7536232449016169989404929 5652174336762127492053697)
            ·
              refine ⟨4239130752571595619040273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5652174336762127492053697 4239130752571595619040273)
              ·
                refine ⟨3179348064428696714280205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4239130752571595619040273 3179348064428696714280205)
                ·
                  refine ⟨1192255524160761267855077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3179348064428696714280205 1192255524160761267855077)
                  ·
                    refine ⟨223547910780142737722827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1192255524160761267855077 223547910780142737722827)
                    ·
                      rfl

theorem cell23_1306074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_1306074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306074 prefixEnd_1306074 := by exact prefixLift 1306074
  have htrace : WordTrace (prefixWord ++ tailWord_1306074) baseStart_1306074 baseEnd_1306074 := by
    simpa [prefixWord, tailWord_1306074, baseEnd_1306074] using wordTrace_append hprefix tailTrace_1306074
  have hstable : (prefixWord ++ tailWord_1306074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306074).length < 2 ^ (prefixWord ++ tailWord_1306074).sum := by decide
  have hdescent : baseEnd_1306074 < baseStart_1306074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306087 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 8]
def baseStart_1306087 : Nat := 118140960795 + 1306087 * 2 ^ 59
def prefixEnd_1306087 : Nat := 4983230072969 + 3 ^ 40 * 1306087 * 2
def baseEnd_1306087 : Nat := 74516711954326295811769

theorem tailTrace_1306087 : CollatzResearch.WordTrace tailWord_1306087 prefixEnd_1306087 74516711954326295811769 := by
  unfold tailWord_1306087
  simp only [CollatzResearch.WordTrace]
  refine ⟨47636906419277335745844515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31757937612851557163896343 47636906419277335745844515)
  ·
    refine ⟨71455359628916003618766773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47636906419277335745844515 71455359628916003618766773)
    ·
      refine ⟨6698939965210875339259385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71455359628916003618766773 6698939965210875339259385)
      ·
        refine ⟨5024204973908156504444539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6698939965210875339259385 5024204973908156504444539)
        ·
          refine ⟨7536307460862234756666809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024204973908156504444539 7536307460862234756666809)
          ·
            refine ⟨5652230595646676067500107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7536307460862234756666809 5652230595646676067500107)
            ·
              refine ⟨8478345893470014101250161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652230595646676067500107 8478345893470014101250161)
              ·
                refine ⟨6358759420102510575937621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8478345893470014101250161 6358759420102510575937621)
                ·
                  refine ⟨74516711954326295811769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6358759420102510575937621 74516711954326295811769)
                  ·
                    rfl

theorem cell23_1306087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 8].length) (baseStart_1306087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306087 prefixEnd_1306087 := by exact prefixLift 1306087
  have htrace : WordTrace (prefixWord ++ tailWord_1306087) baseStart_1306087 baseEnd_1306087 := by
    simpa [prefixWord, tailWord_1306087, baseEnd_1306087] using wordTrace_append hprefix tailTrace_1306087
  have hstable : (prefixWord ++ tailWord_1306087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306087).length < 2 ^ (prefixWord ++ tailWord_1306087).sum := by decide
  have hdescent : baseEnd_1306087 < baseStart_1306087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306101 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1306101 : Nat := 118140960795 + 1306101 * 2 ^ 59
def prefixEnd_1306101 : Nat := 4983230072969 + 3 ^ 40 * 1306101 * 2
def baseEnd_1306101 : Nat := 670657596318099607530857

theorem tailTrace_1306101 : CollatzResearch.WordTrace tailWord_1306101 prefixEnd_1306101 670657596318099607530857 := by
  unfold tailWord_1306101
  simp only [CollatzResearch.WordTrace]
  refine ⟨47637417041226616136854157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31758278027484410757902771 47637417041226616136854157)
  ·
    refine ⟨17864031390459981051320309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47637417041226616136854157 17864031390459981051320309)
    ·
      refine ⟨1674752942855623223561279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17864031390459981051320309 1674752942855623223561279)
      ·
        refine ⟨2512129414283434835341919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674752942855623223561279 2512129414283434835341919)
        ·
          refine ⟨3768194121425152253012879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512129414283434835341919 3768194121425152253012879)
          ·
            refine ⟨5652291182137728379519319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768194121425152253012879 5652291182137728379519319)
            ·
              refine ⟨8478436773206592569278979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652291182137728379519319 8478436773206592569278979)
              ·
                refine ⟨12717655159809888853918469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478436773206592569278979 12717655159809888853918469)
                ·
                  refine ⟨2384560342464354160109713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12717655159809888853918469 2384560342464354160109713)
                  ·
                    refine ⟨1788420256848265620082285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384560342464354160109713 1788420256848265620082285)
                    ·
                      refine ⟨670657596318099607530857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1788420256848265620082285 670657596318099607530857)
                      ·
                        rfl

theorem cell23_1306101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1306101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306101 prefixEnd_1306101 := by exact prefixLift 1306101
  have htrace : WordTrace (prefixWord ++ tailWord_1306101) baseStart_1306101 baseEnd_1306101 := by
    simpa [prefixWord, tailWord_1306101, baseEnd_1306101] using wordTrace_append hprefix tailTrace_1306101
  have hstable : (prefixWord ++ tailWord_1306101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306101).length < 2 ^ (prefixWord ++ tailWord_1306101).sum := by decide
  have hdescent : baseEnd_1306101 < baseStart_1306101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306117 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_1306117 : Nat := 118140960795 + 1306117 * 2 ^ 59
def prefixEnd_1306117 : Nat := 4983230072969 + 3 ^ 40 * 1306117 * 2
def baseEnd_1306117 : Nat := 223555270669523848310261

theorem tailTrace_1306117 : CollatzResearch.WordTrace tailWord_1306117 prefixEnd_1306117 223555270669523848310261 := by
  unfold tailWord_1306117
  simp only [CollatzResearch.WordTrace]
  refine ⟨47638000609168650869436605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31758667072779100579624403 47638000609168650869436605)
  ·
    refine ⟨17864250228438244076038727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47638000609168650869436605 17864250228438244076038727)
    ·
      refine ⟨26796375342657366114058091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17864250228438244076038727 26796375342657366114058091)
      ·
        refine ⟨40194563013986049171087137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26796375342657366114058091 40194563013986049171087137)
        ·
          refine ⟨30145922260489536878315353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40194563013986049171087137 30145922260489536878315353)
          ·
            refine ⟨22609441695367152658736515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30145922260489536878315353 22609441695367152658736515)
            ·
              refine ⟨33914162543050728988104773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22609441695367152658736515 33914162543050728988104773)
              ·
                refine ⟨6358905476822011685269645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33914162543050728988104773 6358905476822011685269645)
                ·
                  refine ⟨2384589553808254381976117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6358905476822011685269645 2384589553808254381976117)
                  ·
                    refine ⟨223555270669523848310261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2384589553808254381976117 223555270669523848310261)
                    ·
                      rfl

theorem cell23_1306117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_1306117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306117 prefixEnd_1306117 := by exact prefixLift 1306117
  have htrace : WordTrace (prefixWord ++ tailWord_1306117) baseStart_1306117 baseEnd_1306117 := by
    simpa [prefixWord, tailWord_1306117, baseEnd_1306117] using wordTrace_append hprefix tailTrace_1306117
  have hstable : (prefixWord ++ tailWord_1306117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306117).length < 2 ^ (prefixWord ++ tailWord_1306117).sum := by decide
  have hdescent : baseEnd_1306117 < baseStart_1306117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306158 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_1306158 : Nat := 118140960795 + 1306158 * 2 ^ 59
def prefixEnd_1306158 : Nat := 4983230072969 + 3 ^ 40 * 1306158 * 2
def baseEnd_1306158 : Nat := 670686864715405884518095

theorem tailTrace_1306158 : CollatzResearch.WordTrace tailWord_1306158 prefixEnd_1306158 670686864715405884518095 := by
  unfold tailWord_1306158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954937000252514358959891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31759664001346743247786085 5954937000252514358959891)
  ·
    refine ⟨8932405500378771538439837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5954937000252514358959891 8932405500378771538439837)
    ·
      refine ⟨3349652062642039326914939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8932405500378771538439837 3349652062642039326914939)
      ·
        refine ⟨5024478093963058990372409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349652062642039326914939 5024478093963058990372409)
        ·
          refine ⟨3768358570472294242779307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5024478093963058990372409 3768358570472294242779307)
          ·
            refine ⟨5652537855708441364168961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768358570472294242779307 5652537855708441364168961)
            ·
              refine ⟨4239403391781331023126721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5652537855708441364168961 4239403391781331023126721)
              ·
                refine ⟨3179552543835998267345041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4239403391781331023126721 3179552543835998267345041)
                ·
                  refine ⟨2384664407876998700508781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179552543835998267345041 2384664407876998700508781)
                  ·
                    refine ⟨894249152953874512690793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384664407876998700508781 894249152953874512690793)
                    ·
                      refine ⟨670686864715405884518095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894249152953874512690793 670686864715405884518095)
                      ·
                        rfl

theorem cell23_1306158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_1306158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306158 prefixEnd_1306158 := by exact prefixLift 1306158
  have htrace : WordTrace (prefixWord ++ tailWord_1306158) baseStart_1306158 baseEnd_1306158 := by
    simpa [prefixWord, tailWord_1306158, baseEnd_1306158] using wordTrace_append hprefix tailTrace_1306158
  have hstable : (prefixWord ++ tailWord_1306158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306158).length < 2 ^ (prefixWord ++ tailWord_1306158).sum := by decide
  have hdescent : baseEnd_1306158 < baseStart_1306158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306165 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_1306165 : Nat := 118140960795 + 1306165 * 2 ^ 59
def prefixEnd_1306165 : Nat := 4983230072969 + 3 ^ 40 * 1306165 * 2
def baseEnd_1306165 : Nat := 670690459079987357130563

theorem tailTrace_1306165 : CollatzResearch.WordTrace tailWord_1306165 prefixEnd_1306165 670690459079987357130563 := by
  unfold tailWord_1306165
  simp only [CollatzResearch.WordTrace]
  refine ⟨47639751312994755067183949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31759834208663170044789299 47639751312994755067183949)
  ·
    refine ⟨17864906742373033150193981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47639751312994755067183949 17864906742373033150193981)
    ·
      refine ⟨6699340028389887431322743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17864906742373033150193981 6699340028389887431322743)
      ·
        refine ⟨10049010042584831146984115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6699340028389887431322743 10049010042584831146984115)
        ·
          refine ⟨15073515063877246720476173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049010042584831146984115 15073515063877246720476173)
          ·
            refine ⟨5652568148953967520178565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15073515063877246720476173 5652568148953967520178565)
            ·
              refine ⟨1059856527928868910033481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5652568148953967520178565 1059856527928868910033481)
              ·
                refine ⟨794892395946651682525111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059856527928868910033481 794892395946651682525111)
                ·
                  refine ⟨1192338593919977523787667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794892395946651682525111 1192338593919977523787667)
                  ·
                    refine ⟨1788507890879966285681501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1192338593919977523787667 1788507890879966285681501)
                    ·
                      refine ⟨670690459079987357130563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1788507890879966285681501 670690459079987357130563)
                      ·
                        rfl

theorem cell23_1306165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_1306165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306165 prefixEnd_1306165 := by exact prefixLift 1306165
  have htrace : WordTrace (prefixWord ++ tailWord_1306165) baseStart_1306165 baseEnd_1306165 := by
    simpa [prefixWord, tailWord_1306165, baseEnd_1306165] using wordTrace_append hprefix tailTrace_1306165
  have hstable : (prefixWord ++ tailWord_1306165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306165).length < 2 ^ (prefixWord ++ tailWord_1306165).sum := by decide
  have hdescent : baseEnd_1306165 < baseStart_1306165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306188 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1306188 : Nat := 118140960795 + 1306188 * 2 ^ 59
def prefixEnd_1306188 : Nat := 4983230072969 + 3 ^ 40 * 1306188 * 2
def baseEnd_1306188 : Nat := 670702269135040767142957

theorem tailTrace_1306188 : CollatzResearch.WordTrace tailWord_1306188 prefixEnd_1306188 670702269135040767142957 := by
  unfold tailWord_1306188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23820295095955714997635609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31760393461274286663514145 23820295095955714997635609)
  ·
    refine ⟨17865221321966786248226707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23820295095955714997635609 17865221321966786248226707)
    ·
      refine ⟨26797831982950179372340061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17865221321966786248226707 26797831982950179372340061)
      ·
        refine ⟨10049186993606317264627523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26797831982950179372340061 10049186993606317264627523)
        ·
          refine ⟨15073780490409475896941285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049186993606317264627523 15073780490409475896941285)
          ·
            refine ⟨2826333841951776730676491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15073780490409475896941285 2826333841951776730676491)
            ·
              refine ⟨4239500762927665096014737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826333841951776730676491 4239500762927665096014737)
              ·
                refine ⟨3179625572195748822011053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4239500762927665096014737 3179625572195748822011053)
                ·
                  refine ⟨1192359589573405808254145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3179625572195748822011053 1192359589573405808254145)
                  ·
                    refine ⟨894269692180054356190609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1192359589573405808254145 894269692180054356190609)
                    ·
                      refine ⟨670702269135040767142957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894269692180054356190609 670702269135040767142957)
                      ·
                        rfl

theorem cell23_1306188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1306188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306188 prefixEnd_1306188 := by exact prefixLift 1306188
  have htrace : WordTrace (prefixWord ++ tailWord_1306188) baseStart_1306188 baseEnd_1306188 := by
    simpa [prefixWord, tailWord_1306188, baseEnd_1306188] using wordTrace_append hprefix tailTrace_1306188
  have hstable : (prefixWord ++ tailWord_1306188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306188).length < 2 ^ (prefixWord ++ tailWord_1306188).sum := by decide
  have hdescent : baseEnd_1306188 < baseStart_1306188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306205 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1306205 : Nat := 118140960795 + 1306205 * 2 ^ 59
def prefixEnd_1306205 : Nat := 4983230072969 + 3 ^ 40 * 1306205 * 2
def baseEnd_1306205 : Nat := 670710998306167200630379

theorem tailTrace_1306205 : CollatzResearch.WordTrace tailWord_1306205 prefixEnd_1306205 670710998306167200630379 := by
  unfold tailWord_1306205
  simp only [CollatzResearch.WordTrace]
  refine ⟨47641210232849841898640069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31760806821899894599093379 47641210232849841898640069)
  ·
    refine ⟨8932726918659345355995013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47641210232849841898640069 8932726918659345355995013)
    ·
      refine ⟨1674886297248627254249065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8932726918659345355995013 1674886297248627254249065)
      ·
        refine ⟨1256164722936470440686799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674886297248627254249065 1256164722936470440686799)
        ·
          refine ⟨1884247084404705661030199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256164722936470440686799 1884247084404705661030199)
          ·
            refine ⟨2826370626607058491545299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884247084404705661030199 2826370626607058491545299)
            ·
              refine ⟨4239555939910587737317949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826370626607058491545299 4239555939910587737317949)
              ·
                refine ⟨1589833477466470401494231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239555939910587737317949 1589833477466470401494231)
                ·
                  refine ⟨2384750216199705602241347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589833477466470401494231 2384750216199705602241347)
                  ·
                    refine ⟨3577125324299558403362021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384750216199705602241347 3577125324299558403362021)
                    ·
                      refine ⟨670710998306167200630379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3577125324299558403362021 670710998306167200630379)
                      ·
                        rfl

theorem cell23_1306205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1306205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306205 prefixEnd_1306205 := by exact prefixLift 1306205
  have htrace : WordTrace (prefixWord ++ tailWord_1306205) baseStart_1306205 baseEnd_1306205 := by
    simpa [prefixWord, tailWord_1306205, baseEnd_1306205] using wordTrace_append hprefix tailTrace_1306205
  have hstable : (prefixWord ++ tailWord_1306205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306205).length < 2 ^ (prefixWord ++ tailWord_1306205).sum := by decide
  have hdescent : baseEnd_1306205 < baseStart_1306205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306261 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_1306261 : Nat := 118140960795 + 1306261 * 2 ^ 59
def prefixEnd_1306261 : Nat := 4983230072969 + 3 ^ 40 * 1306261 * 2
def baseEnd_1306261 : Nat := 670739753222818981530121

theorem tailTrace_1306261 : CollatzResearch.WordTrace tailWord_1306261 prefixEnd_1306261 670739753222818981530121 := by
  unfold tailWord_1306261
  simp only [CollatzResearch.WordTrace]
  refine ⟨47643252720646963462678637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31762168480431308975119091 47643252720646963462678637)
  ·
    refine ⟨17866219770242611298504489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47643252720646963462678637 17866219770242611298504489)
    ·
      refine ⟨13399664827681958473878367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17866219770242611298504489 13399664827681958473878367)
      ·
        refine ⟨20099497241522937710817551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13399664827681958473878367 20099497241522937710817551)
        ·
          refine ⟨30149245862284406566226327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20099497241522937710817551 30149245862284406566226327)
          ·
            refine ⟨45223868793426609849339491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30149245862284406566226327 45223868793426609849339491)
            ·
              refine ⟨67835803190139914774009237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45223868793426609849339491 67835803190139914774009237)
              ·
                refine ⟨3179803274537808505031683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67835803190139914774009237 3179803274537808505031683)
                ·
                  refine ⟨4769704911806712757547525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3179803274537808505031683 4769704911806712757547525)
                  ·
                    refine ⟨894319670963758642040161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4769704911806712757547525 894319670963758642040161)
                    ·
                      refine ⟨670739753222818981530121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894319670963758642040161 670739753222818981530121)
                      ·
                        rfl

theorem cell23_1306261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_1306261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306261 prefixEnd_1306261 := by exact prefixLift 1306261
  have htrace : WordTrace (prefixWord ++ tailWord_1306261) baseStart_1306261 baseEnd_1306261 := by
    simpa [prefixWord, tailWord_1306261, baseEnd_1306261] using wordTrace_append hprefix tailTrace_1306261
  have hstable : (prefixWord ++ tailWord_1306261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306261).length < 2 ^ (prefixWord ++ tailWord_1306261).sum := by decide
  have hdescent : baseEnd_1306261 < baseStart_1306261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306264 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1306264 : Nat := 118140960795 + 1306264 * 2 ^ 59
def prefixEnd_1306264 : Nat := 4983230072969 + 3 ^ 40 * 1306264 * 2
def baseEnd_1306264 : Nat := 670741293664782469792607

theorem tailTrace_1306264 : CollatzResearch.WordTrace tailWord_1306264 prefixEnd_1306264 670741293664782469792607 := by
  unfold tailWord_1306264
  simp only [CollatzResearch.WordTrace]
  refine ⟨23821681069818047487518923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31762241426424063316691897 23821681069818047487518923)
  ·
    refine ⟨35732521604727071231278385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23821681069818047487518923 35732521604727071231278385)
    ·
      refine ⟨26799391203545303423458789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35732521604727071231278385 26799391203545303423458789)
      ·
        refine ⟨5024885850664744391898523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26799391203545303423458789 5024885850664744391898523)
        ·
          refine ⟨7537328775997116587847785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024885850664744391898523 7537328775997116587847785)
          ·
            refine ⟨5652996581997837440885839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7537328775997116587847785 5652996581997837440885839)
            ·
              refine ⟨8479494872996756161328759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652996581997837440885839 8479494872996756161328759)
              ·
                refine ⟨12719242309495134241993139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8479494872996756161328759 12719242309495134241993139)
                ·
                  refine ⟨19078863464242701362989709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12719242309495134241993139 19078863464242701362989709)
                  ·
                    refine ⟨7154573799091013011121141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19078863464242701362989709 7154573799091013011121141)
                    ·
                      refine ⟨670741293664782469792607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7154573799091013011121141 670741293664782469792607)
                      ·
                        rfl

theorem cell23_1306264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1306264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306264 prefixEnd_1306264 := by exact prefixLift 1306264
  have htrace : WordTrace (prefixWord ++ tailWord_1306264) baseStart_1306264 baseEnd_1306264 := by
    simpa [prefixWord, tailWord_1306264, baseEnd_1306264] using wordTrace_append hprefix tailTrace_1306264
  have hstable : (prefixWord ++ tailWord_1306264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306264).length < 2 ^ (prefixWord ++ tailWord_1306264).sum := by decide
  have hdescent : baseEnd_1306264 < baseStart_1306264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306295 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 2, 2, 2]
def baseStart_1306295 : Nat := 118140960795 + 1306295 * 2 ^ 59
def prefixEnd_1306295 : Nat := 4983230072969 + 3 ^ 40 * 1306295 * 2
def baseEnd_1306295 : Nat := 670757211565071848504965

theorem tailTrace_1306295 : CollatzResearch.WordTrace tailWord_1306295 prefixEnd_1306295 670757211565071848504965 := by
  unfold tailWord_1306295
  simp only [CollatzResearch.WordTrace]
  refine ⟨47644492802523787269416339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31762995201682524846277559 47644492802523787269416339)
  ·
    refine ⟨71466739203785680904124509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47644492802523787269416339 71466739203785680904124509)
    ·
      refine ⟨26800027201419630339046691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71466739203785680904124509 26800027201419630339046691)
      ·
        refine ⟨40200040802129445508570037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26800027201419630339046691 40200040802129445508570037)
        ·
          refine ⟨3768753825199635516428441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40200040802129445508570037 3768753825199635516428441)
          ·
            refine ⟨2826565368899726637321331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3768753825199635516428441 2826565368899726637321331)
            ·
              refine ⟨4239848053349589955981997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826565368899726637321331 4239848053349589955981997)
              ·
                refine ⟨1589943020006096233493249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239848053349589955981997 1589943020006096233493249)
                ·
                  refine ⟨1192457265004572175119937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589943020006096233493249 1192457265004572175119937)
                  ·
                    refine ⟨894342948753429131339953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1192457265004572175119937 894342948753429131339953)
                    ·
                      refine ⟨670757211565071848504965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894342948753429131339953 670757211565071848504965)
                      ·
                        rfl

theorem cell23_1306295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_1306295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306295 prefixEnd_1306295 := by exact prefixLift 1306295
  have htrace : WordTrace (prefixWord ++ tailWord_1306295) baseStart_1306295 baseEnd_1306295 := by
    simpa [prefixWord, tailWord_1306295, baseEnd_1306295] using wordTrace_append hprefix tailTrace_1306295
  have hstable : (prefixWord ++ tailWord_1306295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306295).length < 2 ^ (prefixWord ++ tailWord_1306295).sum := by decide
  have hdescent : baseEnd_1306295 < baseStart_1306295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306391 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 8]
def baseStart_1306391 : Nat := 118140960795 + 1306391 * 2 ^ 59
def prefixEnd_1306391 : Nat := 4983230072969 + 3 ^ 40 * 1306391 * 2
def baseEnd_1306391 : Nat := 74534056189767052544947

theorem tailTrace_1306391 : CollatzResearch.WordTrace tailWord_1306391 prefixEnd_1306391 74534056189767052544947 := by
  unfold tailWord_1306391
  simp only [CollatzResearch.WordTrace]
  refine ⟨47647994210175995664911027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31765329473450663776607351 47647994210175995664911027)
  ·
    refine ⟨71471991315263993497366541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47647994210175995664911027 71471991315263993497366541)
    ·
      refine ⟨26801996743223997561512453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71471991315263993497366541 26801996743223997561512453)
      ·
        refine ⟨5025374389354499542783585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26801996743223997561512453 5025374389354499542783585)
        ·
          refine ⟨3769030792015874657087689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5025374389354499542783585 3769030792015874657087689)
          ·
            refine ⟨2826773094011905992815767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3769030792015874657087689 2826773094011905992815767)
            ·
              refine ⟨4240159641017858989223651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826773094011905992815767 4240159641017858989223651)
              ·
                refine ⟨6360239461526788483835477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240159641017858989223651 6360239461526788483835477)
                ·
                  refine ⟨74534056189767052544947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6360239461526788483835477 74534056189767052544947)
                  ·
                    rfl

theorem cell23_1306391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 8].length) (baseStart_1306391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306391 prefixEnd_1306391 := by exact prefixLift 1306391
  have htrace : WordTrace (prefixWord ++ tailWord_1306391) baseStart_1306391 baseEnd_1306391 := by
    simpa [prefixWord, tailWord_1306391, baseEnd_1306391] using wordTrace_append hprefix tailTrace_1306391
  have hstable : (prefixWord ++ tailWord_1306391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306391).length < 2 ^ (prefixWord ++ tailWord_1306391).sum := by decide
  have hdescent : baseEnd_1306391 < baseStart_1306391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306428 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_1306428 : Nat := 118140960795 + 1306428 * 2 ^ 59
def prefixEnd_1306428 : Nat := 4983230072969 + 3 ^ 40 * 1306428 * 2
def baseEnd_1306428 : Nat := 670825504492119828141853

theorem tailTrace_1306428 : CollatzResearch.WordTrace tailWord_1306428 prefixEnd_1306428 670825504492119828141853 := by
  unfold tailWord_1306428
  simp only [CollatzResearch.WordTrace]
  refine ⟨23824671855520975492003969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31766229140694633989338625 23824671855520975492003969)
  ·
    refine ⟨17868503891640731619002977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23824671855520975492003969 17868503891640731619002977)
    ·
      refine ⟨13401377918730548714252233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17868503891640731619002977 13401377918730548714252233)
      ·
        refine ⟨10051033439047911535689175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13401377918730548714252233 10051033439047911535689175)
        ·
          refine ⟨15076550158571867303533763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051033439047911535689175 15076550158571867303533763)
          ·
            refine ⟨22614825237857800955300645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15076550158571867303533763 22614825237857800955300645)
            ·
              refine ⟨4240279732098337679118871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22614825237857800955300645 4240279732098337679118871)
              ·
                refine ⟨6360419598147506518678307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240279732098337679118871 6360419598147506518678307)
                ·
                  refine ⟨9540629397221259778017461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6360419598147506518678307 9540629397221259778017461)
                  ·
                    refine ⟨894434005989493104189137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9540629397221259778017461 894434005989493104189137)
                    ·
                      refine ⟨670825504492119828141853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894434005989493104189137 670825504492119828141853)
                      ·
                        rfl

theorem cell23_1306428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_1306428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306428 prefixEnd_1306428 := by exact prefixLift 1306428
  have htrace : WordTrace (prefixWord ++ tailWord_1306428) baseStart_1306428 baseEnd_1306428 := by
    simpa [prefixWord, tailWord_1306428, baseEnd_1306428] using wordTrace_append hprefix tailTrace_1306428
  have hstable : (prefixWord ++ tailWord_1306428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306428).length < 2 ^ (prefixWord ++ tailWord_1306428).sum := by decide
  have hdescent : baseEnd_1306428 < baseStart_1306428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306452 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1306452 : Nat := 118140960795 + 1306452 * 2 ^ 59
def prefixEnd_1306452 : Nat := 4983230072969 + 3 ^ 40 * 1306452 * 2
def baseEnd_1306452 : Nat := 670837828027827734241743

theorem tailTrace_1306452 : CollatzResearch.WordTrace tailWord_1306452 prefixEnd_1306452 670837828027827734241743 := by
  unfold tailWord_1306452
  simp only [CollatzResearch.WordTrace]
  refine ⟨23825109531477501541440805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31766812708636668721921073 23825109531477501541440805)
  ·
    refine ⟨4467208037152031539020151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23825109531477501541440805 4467208037152031539020151)
    ·
      refine ⟨6700812055728047308530227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4467208037152031539020151 6700812055728047308530227)
      ·
        refine ⟨10051218083592070962795341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6700812055728047308530227 10051218083592070962795341)
        ·
          refine ⟨3769206781347026611048253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10051218083592070962795341 3769206781347026611048253)
          ·
            refine ⟨1413452543005134979143095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3769206781347026611048253 1413452543005134979143095)
            ·
              refine ⟨2120178814507702468714643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413452543005134979143095 2120178814507702468714643)
              ·
                refine ⟨3180268221761553703071965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120178814507702468714643 3180268221761553703071965)
                ·
                  refine ⟨1192600583160582638651987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3180268221761553703071965 1192600583160582638651987)
                  ·
                    refine ⟨1788900874740873957977981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1192600583160582638651987 1788900874740873957977981)
                    ·
                      refine ⟨670837828027827734241743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1788900874740873957977981 670837828027827734241743)
                      ·
                        rfl

theorem cell23_1306452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1306452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306452 prefixEnd_1306452 := by exact prefixLift 1306452
  have htrace : WordTrace (prefixWord ++ tailWord_1306452) baseStart_1306452 baseEnd_1306452 := by
    simpa [prefixWord, tailWord_1306452, baseEnd_1306452] using wordTrace_append hprefix tailTrace_1306452
  have hstable : (prefixWord ++ tailWord_1306452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306452).length < 2 ^ (prefixWord ++ tailWord_1306452).sum := by decide
  have hdescent : baseEnd_1306452 < baseStart_1306452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306471 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1306471 : Nat := 118140960795 + 1306471 * 2 ^ 59
def prefixEnd_1306471 : Nat := 4983230072969 + 3 ^ 40 * 1306471 * 2
def baseEnd_1306471 : Nat := 670847584160263159904155

theorem tailTrace_1306471 : CollatzResearch.WordTrace tailWord_1306471 prefixEnd_1306471 670847584160263159904155 := by
  unfold tailWord_1306471
  simp only [CollatzResearch.WordTrace]
  refine ⟨47650912049886169327823267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31767274699924112885215511 47650912049886169327823267)
  ·
    refine ⟨71476368074829253991734901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47650912049886169327823267 71476368074829253991734901)
    ·
      refine ⟨6700909507015242561725147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71476368074829253991734901 6700909507015242561725147)
      ·
        refine ⟨10051364260522863842587721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6700909507015242561725147 10051364260522863842587721)
        ·
          refine ⟨7538523195392147881940791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10051364260522863842587721 7538523195392147881940791)
          ·
            refine ⟨11307784793088221822911187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7538523195392147881940791 11307784793088221822911187)
            ·
              refine ⟨16961677189632332734366781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11307784793088221822911187 16961677189632332734366781)
              ·
                refine ⟨6360628946112124775387543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16961677189632332734366781 6360628946112124775387543)
                ·
                  refine ⟨9540943419168187163081315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6360628946112124775387543 9540943419168187163081315)
                  ·
                    refine ⟨14311415128752280744621973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9540943419168187163081315 14311415128752280744621973)
                    ·
                      refine ⟨670847584160263159904155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14311415128752280744621973 670847584160263159904155)
                      ·
                        rfl

theorem cell23_1306471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1306471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306471 prefixEnd_1306471 := by exact prefixLift 1306471
  have htrace : WordTrace (prefixWord ++ tailWord_1306471) baseStart_1306471 baseEnd_1306471 := by
    simpa [prefixWord, tailWord_1306471, baseEnd_1306471] using wordTrace_append hprefix tailTrace_1306471
  have hstable : (prefixWord ++ tailWord_1306471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306471).length < 2 ^ (prefixWord ++ tailWord_1306471).sum := by decide
  have hdescent : baseEnd_1306471 < baseStart_1306471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306525 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1306525 : Nat := 118140960795 + 1306525 * 2 ^ 59
def prefixEnd_1306525 : Nat := 4983230072969 + 3 ^ 40 * 1306525 * 2
def baseEnd_1306525 : Nat := 670875312115605948628907

theorem tailTrace_1306525 : CollatzResearch.WordTrace tailWord_1306525 prefixEnd_1306525 670875312115605948628907 := by
  unfold tailWord_1306525
  simp only [CollatzResearch.WordTrace]
  refine ⟨47652881591690536550289029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31768587727793691033526019 47652881591690536550289029)
  ·
    refine ⟨8934915298441975603179193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47652881591690536550289029 8934915298441975603179193)
    ·
      refine ⟨6701186473831481702384395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8934915298441975603179193 6701186473831481702384395)
      ·
        refine ⟨10051779710747222553576593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701186473831481702384395 10051779710747222553576593)
        ·
          refine ⟨7538834783060416915182445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10051779710747222553576593 7538834783060416915182445)
          ·
            refine ⟨2827063043647656343193417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7538834783060416915182445 2827063043647656343193417)
            ·
              refine ⟨2120297282735742257395063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827063043647656343193417 2120297282735742257395063)
              ·
                refine ⟨3180445924103613386092595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120297282735742257395063 3180445924103613386092595)
                ·
                  refine ⟨4770668886155420079138893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180445924103613386092595 4770668886155420079138893)
                  ·
                    refine ⟨1789000832308282529677085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4770668886155420079138893 1789000832308282529677085)
                    ·
                      refine ⟨670875312115605948628907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1789000832308282529677085 670875312115605948628907)
                      ·
                        rfl

theorem cell23_1306525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1306525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306525 prefixEnd_1306525 := by exact prefixLift 1306525
  have htrace : WordTrace (prefixWord ++ tailWord_1306525) baseStart_1306525 baseEnd_1306525 := by
    simpa [prefixWord, tailWord_1306525, baseEnd_1306525] using wordTrace_append hprefix tailTrace_1306525
  have hstable : (prefixWord ++ tailWord_1306525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306525).length < 2 ^ (prefixWord ++ tailWord_1306525).sum := by decide
  have hdescent : baseEnd_1306525 < baseStart_1306525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306526 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1306526 : Nat := 118140960795 + 1306526 * 2 ^ 59
def prefixEnd_1306526 : Nat := 4983230072969 + 3 ^ 40 * 1306526 * 2
def baseEnd_1306526 : Nat := 670875825596260444716403

theorem tailTrace_1306526 : CollatzResearch.WordTrace tailWord_1306526 prefixEnd_1306526 670875825596260444716403 := by
  unfold tailWord_1306526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956614758085864215134429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31768612043124609147383621 5956614758085864215134429)
  ·
    refine ⟨2233730534282199080675411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5956614758085864215134429 2233730534282199080675411)
    ·
      refine ⟨3350595801423298621013117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233730534282199080675411 3350595801423298621013117)
      ·
        refine ⟨1256473425533736982879919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3350595801423298621013117 1256473425533736982879919)
        ·
          refine ⟨1884710138300605474319879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256473425533736982879919 1884710138300605474319879)
          ·
            refine ⟨2827065207450908211479819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884710138300605474319879 2827065207450908211479819)
            ·
              refine ⟨4240597811176362317219729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827065207450908211479819 4240597811176362317219729)
              ·
                refine ⟨3180448358382271737914797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4240597811176362317219729 3180448358382271737914797)
                ·
                  refine ⟨1192668134393351901718049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3180448358382271737914797 1192668134393351901718049)
                  ·
                    refine ⟨894501100795013926288537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1192668134393351901718049 894501100795013926288537)
                    ·
                      refine ⟨670875825596260444716403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894501100795013926288537 670875825596260444716403)
                      ·
                        rfl

theorem cell23_1306526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1306526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306526 prefixEnd_1306526 := by exact prefixLift 1306526
  have htrace : WordTrace (prefixWord ++ tailWord_1306526) baseStart_1306526 baseEnd_1306526 := by
    simpa [prefixWord, tailWord_1306526, baseEnd_1306526] using wordTrace_append hprefix tailTrace_1306526
  have hstable : (prefixWord ++ tailWord_1306526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306526).length < 2 ^ (prefixWord ++ tailWord_1306526).sum := by decide
  have hdescent : baseEnd_1306526 < baseStart_1306526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306531 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1306531 : Nat := 118140960795 + 1306531 * 2 ^ 59
def prefixEnd_1306531 : Nat := 4983230072969 + 3 ^ 40 * 1306531 * 2
def baseEnd_1306531 : Nat := 670878392999532925153879

theorem tailTrace_1306531 : CollatzResearch.WordTrace tailWord_1306531 prefixEnd_1306531 670878392999532925153879 := by
  unfold tailWord_1306531
  simp only [CollatzResearch.WordTrace]
  refine ⟨47653100429668799575007447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31768733619779199716671631 47653100429668799575007447)
  ·
    refine ⟨71479650644503199362511171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47653100429668799575007447 71479650644503199362511171)
    ·
      refine ⟨107219475966754799043766757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71479650644503199362511171 107219475966754799043766757)
      ·
        refine ⟨20103651743766524820706267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107219475966754799043766757 20103651743766524820706267)
        ·
          refine ⟨30155477615649787231059401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20103651743766524820706267 30155477615649787231059401)
          ·
            refine ⟨22616608211737340423294551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30155477615649787231059401 22616608211737340423294551)
            ·
              refine ⟨33924912317606010634941827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22616608211737340423294551 33924912317606010634941827)
              ·
                refine ⟨50887368476409015952412741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33924912317606010634941827 50887368476409015952412741)
                ·
                  refine ⟨9541381589326690491077389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50887368476409015952412741 9541381589326690491077389)
                  ·
                    refine ⟨3578018095997508934154021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9541381589326690491077389 3578018095997508934154021)
                    ·
                      refine ⟨670878392999532925153879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3578018095997508934154021 670878392999532925153879)
                      ·
                        rfl

theorem cell23_1306531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1306531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306531 prefixEnd_1306531 := by exact prefixLift 1306531
  have htrace : WordTrace (prefixWord ++ tailWord_1306531) baseStart_1306531 baseEnd_1306531 := by
    simpa [prefixWord, tailWord_1306531, baseEnd_1306531] using wordTrace_append hprefix tailTrace_1306531
  have hstable : (prefixWord ++ tailWord_1306531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306531).length < 2 ^ (prefixWord ++ tailWord_1306531).sum := by decide
  have hdescent : baseEnd_1306531 < baseStart_1306531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306551 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_1306551 : Nat := 118140960795 + 1306551 * 2 ^ 59
def prefixEnd_1306551 : Nat := 4983230072969 + 3 ^ 40 * 1306551 * 2
def baseEnd_1306551 : Nat := 670888662612622846903787

theorem tailTrace_1306551 : CollatzResearch.WordTrace tailWord_1306551 prefixEnd_1306551 670888662612622846903787 := by
  unfold tailWord_1306551
  simp only [CollatzResearch.WordTrace]
  refine ⟨47653829889596342990735507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31769219926397561993823671 47653829889596342990735507)
  ·
    refine ⟨71480744834394514486103261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47653829889596342990735507 71480744834394514486103261)
    ·
      refine ⟨26805279312897942932288723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71480744834394514486103261 26805279312897942932288723)
      ·
        refine ⟨40207918969346914398433085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26805279312897942932288723 40207918969346914398433085)
        ·
          refine ⟨15077969613505092899412407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40207918969346914398433085 15077969613505092899412407)
          ·
            refine ⟨22616954420257639349118611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15077969613505092899412407 22616954420257639349118611)
            ·
              refine ⟨33925431630386459023677917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22616954420257639349118611 33925431630386459023677917)
              ·
                refine ⟨12722036861394922133879219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33925431630386459023677917 12722036861394922133879219)
                ·
                  refine ⟨19083055292092383200818829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12722036861394922133879219 19083055292092383200818829)
                  ·
                    refine ⟨7156145734534643700307061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19083055292092383200818829 7156145734534643700307061)
                    ·
                      refine ⟨670888662612622846903787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7156145734534643700307061 670888662612622846903787)
                      ·
                        rfl

theorem cell23_1306551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_1306551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306551 prefixEnd_1306551 := by exact prefixLift 1306551
  have htrace : WordTrace (prefixWord ++ tailWord_1306551) baseStart_1306551 baseEnd_1306551 := by
    simpa [prefixWord, tailWord_1306551, baseEnd_1306551] using wordTrace_append hprefix tailTrace_1306551
  have hstable : (prefixWord ++ tailWord_1306551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306551).length < 2 ^ (prefixWord ++ tailWord_1306551).sum := by decide
  have hdescent : baseEnd_1306551 < baseStart_1306551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306558 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1306558 : Nat := 118140960795 + 1306558 * 2 ^ 59
def prefixEnd_1306558 : Nat := 4983230072969 + 3 ^ 40 * 1306558 * 2
def baseEnd_1306558 : Nat := 223630752325734773172085

theorem tailTrace_1306558 : CollatzResearch.WordTrace tailWord_1306558 prefixEnd_1306558 223630752325734773172085 := by
  unfold tailWord_1306558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956760650071372898280041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31769390133713988790826885 5956760650071372898280041)
  ·
    refine ⟨4467570487553529673710031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5956760650071372898280041 4467570487553529673710031)
    ·
      refine ⟨6701355731330294510565047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4467570487553529673710031 6701355731330294510565047)
      ·
        refine ⟨10052033596995441765847571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701355731330294510565047 10052033596995441765847571)
        ·
          refine ⟨15078050395493162648771357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10052033596995441765847571 15078050395493162648771357)
          ·
            refine ⟨5654268898309935993289259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15078050395493162648771357 5654268898309935993289259)
            ·
              refine ⟨8481403347464903989933889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5654268898309935993289259 8481403347464903989933889)
              ·
                refine ⟨6361052510598677992450417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481403347464903989933889 6361052510598677992450417)
                ·
                  refine ⟨4770789382949008494337813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361052510598677992450417 4770789382949008494337813)
                  ·
                    refine ⟨223630752325734773172085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4770789382949008494337813 223630752325734773172085)
                    ·
                      rfl

theorem cell23_1306558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1306558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306558 prefixEnd_1306558 := by exact prefixLift 1306558
  have htrace : WordTrace (prefixWord ++ tailWord_1306558) baseStart_1306558 baseEnd_1306558 := by
    simpa [prefixWord, tailWord_1306558, baseEnd_1306558] using wordTrace_append hprefix tailTrace_1306558
  have hstable : (prefixWord ++ tailWord_1306558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306558).length < 2 ^ (prefixWord ++ tailWord_1306558).sum := by decide
  have hdescent : baseEnd_1306558 < baseStart_1306558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306611 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_1306611 : Nat := 118140960795 + 1306611 * 2 ^ 59
def prefixEnd_1306611 : Nat := 4983230072969 + 3 ^ 40 * 1306611 * 2
def baseEnd_1306611 : Nat := 670919471451892612153511

theorem tailTrace_1306611 : CollatzResearch.WordTrace tailWord_1306611 prefixEnd_1306611 670919471451892612153511 := by
  unfold tailWord_1306611
  simp only [CollatzResearch.WordTrace]
  refine ⟨47656018269378973237919687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31770678846252648825279791 47656018269378973237919687)
  ·
    refine ⟨71484027404068459856879531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47656018269378973237919687 71484027404068459856879531)
    ·
      refine ⟨107226041106102689785319297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71484027404068459856879531 107226041106102689785319297)
      ·
        refine ⟨80419530829577017338989473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107226041106102689785319297 80419530829577017338989473)
        ·
          refine ⟨60314648122182763004242105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80419530829577017338989473 60314648122182763004242105)
          ·
            refine ⟨45235986091637072253181579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60314648122182763004242105 45235986091637072253181579)
            ·
              refine ⟨67853979137455608379772369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45235986091637072253181579 67853979137455608379772369)
              ·
                refine ⟨50890484353091706284829277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67853979137455608379772369 50890484353091706284829277)
                ·
                  refine ⟨19083931632409389856810979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50890484353091706284829277 19083931632409389856810979)
                  ·
                    refine ⟨28625897448614084785216469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19083931632409389856810979 28625897448614084785216469)
                    ·
                      refine ⟨670919471451892612153511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28625897448614084785216469 670919471451892612153511)
                      ·
                        rfl

theorem cell23_1306611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_1306611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306611 prefixEnd_1306611 := by exact prefixLift 1306611
  have htrace : WordTrace (prefixWord ++ tailWord_1306611) baseStart_1306611 baseEnd_1306611 := by
    simpa [prefixWord, tailWord_1306611, baseEnd_1306611] using wordTrace_append hprefix tailTrace_1306611
  have hstable : (prefixWord ++ tailWord_1306611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306611).length < 2 ^ (prefixWord ++ tailWord_1306611).sum := by decide
  have hdescent : baseEnd_1306611 < baseStart_1306611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306622 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_1306622 : Nat := 118140960795 + 1306622 * 2 ^ 59
def prefixEnd_1306622 : Nat := 4983230072969 + 3 ^ 40 * 1306622 * 2
def baseEnd_1306622 : Nat := 74547235526565785457329

theorem tailTrace_1306622 : CollatzResearch.WordTrace tailWord_1306622 prefixEnd_1306622 74547235526565785457329 := by
  unfold tailWord_1306622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957052434042390264571265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31770946314892748077713413 5957052434042390264571265)
  ·
    refine ⟨4467789325531792698428449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5957052434042390264571265 4467789325531792698428449)
    ·
      refine ⟨3350841994148844523821337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4467789325531792698428449 3350841994148844523821337)
      ·
        refine ⟨2513131495611633392866003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3350841994148844523821337 2513131495611633392866003)
        ·
          refine ⟨3769697243417450089299005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2513131495611633392866003 3769697243417450089299005)
          ·
            refine ⟨1413636466281543783487127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3769697243417450089299005 1413636466281543783487127)
            ·
              refine ⟨2120454699422315675230691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413636466281543783487127 2120454699422315675230691)
              ·
                refine ⟨3180682049133473512846037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120454699422315675230691 3180682049133473512846037)
                ·
                  refine ⟨74547235526565785457329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3180682049133473512846037 74547235526565785457329)
                  ·
                    rfl

theorem cell23_1306622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_1306622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306622 prefixEnd_1306622 := by exact prefixLift 1306622
  have htrace : WordTrace (prefixWord ++ tailWord_1306622) baseStart_1306622 baseEnd_1306622 := by
    simpa [prefixWord, tailWord_1306622, baseEnd_1306622] using wordTrace_append hprefix tailTrace_1306622
  have hstable : (prefixWord ++ tailWord_1306622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306622).length < 2 ^ (prefixWord ++ tailWord_1306622).sum := by decide
  have hdescent : baseEnd_1306622 < baseStart_1306622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306625 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_1306625 : Nat := 118140960795 + 1306625 * 2 ^ 59
def prefixEnd_1306625 : Nat := 4983230072969 + 3 ^ 40 * 1306625 * 2
def baseEnd_1306625 : Nat := 670926660181055557378447

theorem tailTrace_1306625 : CollatzResearch.WordTrace tailWord_1306625 prefixEnd_1306625 670926660181055557378447 := by
  unfold tailWord_1306625
  simp only [CollatzResearch.WordTrace]
  refine ⟨47656528891328253628929329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31771019260885502419286219 47656528891328253628929329)
  ·
    refine ⟨35742396668496190221696997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47656528891328253628929329 35742396668496190221696997)
    ·
      refine ⟨6701699375343035666568187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35742396668496190221696997 6701699375343035666568187)
      ·
        refine ⟨10052549063014553499852281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701699375343035666568187 10052549063014553499852281)
        ·
          refine ⟨7539411797260915124889211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10052549063014553499852281 7539411797260915124889211)
          ·
            refine ⟨11309117695891372687333817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539411797260915124889211 11309117695891372687333817)
            ·
              refine ⟨8481838271918529515500363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11309117695891372687333817 8481838271918529515500363)
              ·
                refine ⟨12722757407877794273250545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8481838271918529515500363 12722757407877794273250545)
                ·
                  refine ⟨9542068055908345704937909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12722757407877794273250545 9542068055908345704937909)
                  ·
                    refine ⟨894568880241407409837929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9542068055908345704937909 894568880241407409837929)
                    ·
                      refine ⟨670926660181055557378447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894568880241407409837929 670926660181055557378447)
                      ·
                        rfl

theorem cell23_1306625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_1306625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306625 prefixEnd_1306625 := by exact prefixLift 1306625
  have htrace : WordTrace (prefixWord ++ tailWord_1306625) baseStart_1306625 baseEnd_1306625 := by
    simpa [prefixWord, tailWord_1306625, baseEnd_1306625] using wordTrace_append hprefix tailTrace_1306625
  have hstable : (prefixWord ++ tailWord_1306625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306625).length < 2 ^ (prefixWord ++ tailWord_1306625).sum := by decide
  have hdescent : baseEnd_1306625 < baseStart_1306625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306655 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_1306655 : Nat := 118140960795 + 1306655 * 2 ^ 59
def prefixEnd_1306655 : Nat := 4983230072969 + 3 ^ 40 * 1306655 * 2
def baseEnd_1306655 : Nat := 670942064600690440003309

theorem tailTrace_1306655 : CollatzResearch.WordTrace tailWord_1306655 prefixEnd_1306655 670942064600690440003309 := by
  unfold tailWord_1306655
  simp only [CollatzResearch.WordTrace]
  refine ⟨47657623081219568752521419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31771748720813045835014279 47657623081219568752521419)
  ·
    refine ⟨71486434621829353128782129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47657623081219568752521419 71486434621829353128782129)
    ·
      refine ⟨53614825966372014846586597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71486434621829353128782129 53614825966372014846586597)
      ·
        refine ⟨10052779868694752783734987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53614825966372014846586597 10052779868694752783734987)
        ·
          refine ⟨15079169803042129175602481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10052779868694752783734987 15079169803042129175602481)
          ·
            refine ⟨11309377352281596881701861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15079169803042129175602481 11309377352281596881701861)
            ·
              refine ⟨2120508253552799415319099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11309377352281596881701861 2120508253552799415319099)
              ·
                refine ⟨3180762380329199122978649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120508253552799415319099 3180762380329199122978649)
                ·
                  refine ⟨2385571785246899342233987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3180762380329199122978649 2385571785246899342233987)
                  ·
                    refine ⟨3578357677870349013350981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2385571785246899342233987 3578357677870349013350981)
                    ·
                      refine ⟨670942064600690440003309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3578357677870349013350981 670942064600690440003309)
                      ·
                        rfl

theorem cell23_1306655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_1306655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306655 prefixEnd_1306655 := by exact prefixLift 1306655
  have htrace : WordTrace (prefixWord ++ tailWord_1306655) baseStart_1306655 baseEnd_1306655 := by
    simpa [prefixWord, tailWord_1306655, baseEnd_1306655] using wordTrace_append hprefix tailTrace_1306655
  have hstable : (prefixWord ++ tailWord_1306655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306655).length < 2 ^ (prefixWord ++ tailWord_1306655).sum := by decide
  have hdescent : baseEnd_1306655 < baseStart_1306655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306675 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 3]
def baseStart_1306675 : Nat := 118140960795 + 1306675 * 2 ^ 59
def prefixEnd_1306675 : Nat := 4983230072969 + 3 ^ 40 * 1306675 * 2
def baseEnd_1306675 : Nat := 670952334213780361753217

theorem tailTrace_1306675 : CollatzResearch.WordTrace tailWord_1306675 prefixEnd_1306675 670952334213780361753217 := by
  unfold tailWord_1306675
  simp only [CollatzResearch.WordTrace]
  refine ⟨47658352541147112168249479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31772235027431408112166319 47658352541147112168249479)
  ·
    refine ⟨71487528811720668252374219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47658352541147112168249479 71487528811720668252374219)
    ·
      refine ⟨107231293217581002378561329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71487528811720668252374219 107231293217581002378561329)
      ·
        refine ⟨80423469913185751783920997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107231293217581002378561329 80423469913185751783920997)
        ·
          refine ⟨15079400608722328459485187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80423469913185751783920997 15079400608722328459485187)
          ·
            refine ⟨22619100913083492689227781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15079400608722328459485187 22619100913083492689227781)
            ·
              refine ⟨4241081421203154879230209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22619100913083492689227781 4241081421203154879230209)
              ·
                refine ⟨3180811065902366159422657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241081421203154879230209 3180811065902366159422657)
                ·
                  refine ⟨2385608299426774619566993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3180811065902366159422657 2385608299426774619566993)
                  ·
                    refine ⟨1789206224570080964675245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385608299426774619566993 1789206224570080964675245)
                    ·
                      refine ⟨670952334213780361753217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1789206224570080964675245 670952334213780361753217)
                      ·
                        rfl

theorem cell23_1306675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_1306675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306675 prefixEnd_1306675 := by exact prefixLift 1306675
  have htrace : WordTrace (prefixWord ++ tailWord_1306675) baseStart_1306675 baseEnd_1306675 := by
    simpa [prefixWord, tailWord_1306675, baseEnd_1306675] using wordTrace_append hprefix tailTrace_1306675
  have hstable : (prefixWord ++ tailWord_1306675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306675).length < 2 ^ (prefixWord ++ tailWord_1306675).sum := by decide
  have hdescent : baseEnd_1306675 < baseStart_1306675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306755 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 1, 6]
def baseStart_1306755 : Nat := 118140960795 + 1306755 * 2 ^ 59
def prefixEnd_1306755 : Nat := 4983230072969 + 3 ^ 40 * 1306755 * 2
def baseEnd_1306755 : Nat := 223664470888713349584283

theorem tailTrace_1306755 : CollatzResearch.WordTrace tailWord_1306755 prefixEnd_1306755 223664470888713349584283 := by
  unfold tailWord_1306755
  simp only [CollatzResearch.WordTrace]
  refine ⟨47661270380857285831161719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31774180253904857220774479 47661270380857285831161719)
  ·
    refine ⟨71491905571285928746742579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47661270380857285831161719 71491905571285928746742579)
    ·
      refine ⟨107237858356928893120113869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71491905571285928746742579 107237858356928893120113869)
      ·
        refine ⟨40214196883848334920042701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107237858356928893120113869 40214196883848334920042701)
        ·
          refine ⟨15080323831443125595016013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40214196883848334920042701 15080323831443125595016013)
          ·
            refine ⟨5655121436791172098131005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15080323831443125595016013 5655121436791172098131005)
            ·
              refine ⟨2120670538796689536799127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5655121436791172098131005 2120670538796689536799127)
              ·
                refine ⟨3181005808195034305198691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120670538796689536799127 3181005808195034305198691)
                ·
                  refine ⟨4771508712292551457798037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181005808195034305198691 4771508712292551457798037)
                  ·
                    refine ⟨223664470888713349584283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4771508712292551457798037 223664470888713349584283)
                    ·
                      rfl

theorem cell23_1306755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 6].length) (baseStart_1306755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306755 prefixEnd_1306755 := by exact prefixLift 1306755
  have htrace : WordTrace (prefixWord ++ tailWord_1306755) baseStart_1306755 baseEnd_1306755 := by
    simpa [prefixWord, tailWord_1306755, baseEnd_1306755] using wordTrace_append hprefix tailTrace_1306755
  have hstable : (prefixWord ++ tailWord_1306755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306755).length < 2 ^ (prefixWord ++ tailWord_1306755).sum := by decide
  have hdescent : baseEnd_1306755 < baseStart_1306755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306762 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1306762 : Nat := 118140960795 + 1306762 * 2 ^ 59
def prefixEnd_1306762 : Nat := 4983230072969 + 3 ^ 40 * 1306762 * 2
def baseEnd_1306762 : Nat := 670997007030721521365317

theorem tailTrace_1306762 : CollatzResearch.WordTrace tailWord_1306762 prefixEnd_1306762 670997007030721521365317 := by
  unfold tailWord_1306762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11915381422957981506666635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31774350461221284017777693 11915381422957981506666635)
  ·
    refine ⟨17873072134436972259999953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11915381422957981506666635 17873072134436972259999953)
    ·
      refine ⟨13404804100827729194999965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17873072134436972259999953 13404804100827729194999965)
      ·
        refine ⟨5026801537810398448124987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13404804100827729194999965 5026801537810398448124987)
        ·
          refine ⟨7540202306715597672187481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026801537810398448124987 7540202306715597672187481)
          ·
            refine ⟨5655151730036698254140611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7540202306715597672187481 5655151730036698254140611)
            ·
              refine ⟨8482727595055047381210917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655151730036698254140611 8482727595055047381210917)
              ·
                refine ⟨1590511424072821383977047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8482727595055047381210917 1590511424072821383977047)
                ·
                  refine ⟨2385767136109232075965571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590511424072821383977047 2385767136109232075965571)
                  ·
                    refine ⟨3578650704163848113948357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2385767136109232075965571 3578650704163848113948357)
                    ·
                      refine ⟨670997007030721521365317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3578650704163848113948357 670997007030721521365317)
                      ·
                        rfl

theorem cell23_1306762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1306762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306762 prefixEnd_1306762 := by exact prefixLift 1306762
  have htrace : WordTrace (prefixWord ++ tailWord_1306762) baseStart_1306762 baseEnd_1306762 := by
    simpa [prefixWord, tailWord_1306762, baseEnd_1306762] using wordTrace_append hprefix tailTrace_1306762
  have hstable : (prefixWord ++ tailWord_1306762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306762).length < 2 ^ (prefixWord ++ tailWord_1306762).sum := by decide
  have hdescent : baseEnd_1306762 < baseStart_1306762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306768 : List Nat := [2, 1, 1, 1, 1, 1, 7, 9]
def baseStart_1306768 : Nat := 118140960795 + 1306768 * 2 ^ 59
def prefixEnd_1306768 : Nat := 4983230072969 + 3 ^ 40 * 1306768 * 2
def baseEnd_1306768 : Nat := 24851855107949944366307

theorem tailTrace_1306768 : CollatzResearch.WordTrace tailWord_1306768 prefixEnd_1306768 24851855107949944366307 := by
  unfold tailWord_1306768
  simp only [CollatzResearch.WordTrace]
  refine ⟨23830872264905094525692479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31774496353206792700923305 23830872264905094525692479)
  ·
    refine ⟨35746308397357641788538719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23830872264905094525692479 35746308397357641788538719)
    ·
      refine ⟨53619462596036462682808079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35746308397357641788538719 53619462596036462682808079)
      ·
        refine ⟨80429193894054694024212119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53619462596036462682808079 80429193894054694024212119)
        ·
          refine ⟨120643790841082041036318179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80429193894054694024212119 120643790841082041036318179)
          ·
            refine ⟨180965686261623061554477269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120643790841082041036318179 180965686261623061554477269)
            ·
              refine ⟨4241383271756790505183061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 180965686261623061554477269 4241383271756790505183061)
              ·
                refine ⟨24851855107949944366307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4241383271756790505183061 24851855107949944366307)
                ·
                  rfl

theorem cell23_1306768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 9].length) (baseStart_1306768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306768 prefixEnd_1306768 := by exact prefixLift 1306768
  have htrace : WordTrace (prefixWord ++ tailWord_1306768) baseStart_1306768 baseEnd_1306768 := by
    simpa [prefixWord, tailWord_1306768, baseEnd_1306768] using wordTrace_append hprefix tailTrace_1306768
  have hstable : (prefixWord ++ tailWord_1306768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306768).length < 2 ^ (prefixWord ++ tailWord_1306768).sum := by decide
  have hdescent : baseEnd_1306768 < baseStart_1306768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306785 : List Nat := [1, 2, 3, 3, 1, 4, 9]
def baseStart_1306785 : Nat := 118140960795 + 1306785 * 2 ^ 59
def prefixEnd_1306785 : Nat := 4983230072969 + 3 ^ 40 * 1306785 * 2
def baseEnd_1306785 : Nat := 8284059470194752239231

theorem tailTrace_1306785 : CollatzResearch.WordTrace tailWord_1306785 prefixEnd_1306785 8284059470194752239231 := by
  unfold tailWord_1306785
  simp only [CollatzResearch.WordTrace]
  refine ⟨47662364570748600954753809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31774909713832400636502539 47662364570748600954753809)
  ·
    refine ⟨35746773428061450716065357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47662364570748600954753809 35746773428061450716065357)
    ·
      refine ⟨13405040035523044018524509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35746773428061450716065357 13405040035523044018524509)
      ·
        refine ⟨5026890013321141506946691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13405040035523044018524509 5026890013321141506946691)
        ·
          refine ⟨7540335019981712260420037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026890013321141506946691 7540335019981712260420037)
          ·
            refine ⟨1413812816246571048828757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7540335019981712260420037 1413812816246571048828757)
            ·
              refine ⟨8284059470194752239231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1413812816246571048828757 8284059470194752239231)
              ·
                rfl

theorem cell23_1306785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 9].length) (baseStart_1306785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306785 prefixEnd_1306785 := by exact prefixLift 1306785
  have htrace : WordTrace (prefixWord ++ tailWord_1306785) baseStart_1306785 baseEnd_1306785 := by
    simpa [prefixWord, tailWord_1306785, baseEnd_1306785] using wordTrace_append hprefix tailTrace_1306785
  have hstable : (prefixWord ++ tailWord_1306785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306785).length < 2 ^ (prefixWord ++ tailWord_1306785).sum := by decide
  have hdescent : baseEnd_1306785 < baseStart_1306785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306852 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_1306852 : Nat := 118140960795 + 1306852 * 2 ^ 59
def prefixEnd_1306852 : Nat := 4983230072969 + 3 ^ 40 * 1306852 * 2
def baseEnd_1306852 : Nat := 671043220289626169239903

theorem tailTrace_1306852 : CollatzResearch.WordTrace tailWord_1306852 prefixEnd_1306852 671043220289626169239903 := by
  unfold tailWord_1306852
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832404130752935698721405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31776538841003914264961873 23832404130752935698721405)
  ·
    refine ⟨8937151549032350887020527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23832404130752935698721405 8937151549032350887020527)
    ·
      refine ⟨13405727323548526330530791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8937151549032350887020527 13405727323548526330530791)
      ·
        refine ⟨20108590985322789495796187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13405727323548526330530791 20108590985322789495796187)
        ·
          refine ⟨30162886477984184243694281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20108590985322789495796187 30162886477984184243694281)
          ·
            refine ⟨22622164858488138182770711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30162886477984184243694281 22622164858488138182770711)
            ·
              refine ⟨33933247287732207274156067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22622164858488138182770711 33933247287732207274156067)
              ·
                refine ⟨50899870931598310911234101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33933247287732207274156067 50899870931598310911234101)
                ·
                  refine ⟨4771862899837341647928197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50899870931598310911234101 4771862899837341647928197)
                  ·
                    refine ⟨894724293719501558986537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4771862899837341647928197 894724293719501558986537)
                    ·
                      refine ⟨671043220289626169239903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894724293719501558986537 671043220289626169239903)
                      ·
                        rfl

theorem cell23_1306852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_1306852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306852 prefixEnd_1306852 := by exact prefixLift 1306852
  have htrace : WordTrace (prefixWord ++ tailWord_1306852) baseStart_1306852 baseEnd_1306852 := by
    simpa [prefixWord, tailWord_1306852, baseEnd_1306852] using wordTrace_append hprefix tailTrace_1306852
  have hstable : (prefixWord ++ tailWord_1306852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306852).length < 2 ^ (prefixWord ++ tailWord_1306852).sum := by decide
  have hdescent : baseEnd_1306852 < baseStart_1306852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306865 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1306865 : Nat := 118140960795 + 1306865 * 2 ^ 59
def prefixEnd_1306865 : Nat := 4983230072969 + 3 ^ 40 * 1306865 * 2
def baseEnd_1306865 : Nat := 671049895538134618377343

theorem tailTrace_1306865 : CollatzResearch.WordTrace tailWord_1306865 prefixEnd_1306865 671049895538134618377343 := by
  unfold tailWord_1306865
  simp only [CollatzResearch.WordTrace]
  refine ⟨47665282410458774617666049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31776854940305849745110699 47665282410458774617666049)
  ·
    refine ⟨35748961807844080963249537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47665282410458774617666049 35748961807844080963249537)
    ·
      refine ⟨26811721355883060722437153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35748961807844080963249537 26811721355883060722437153)
      ·
        refine ⟨20108791016912295541827865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26811721355883060722437153 20108791016912295541827865)
        ·
          refine ⟨15081593262684221656370899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20108791016912295541827865 15081593262684221656370899)
          ·
            refine ⟨22622389894026332484556349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15081593262684221656370899 22622389894026332484556349)
            ·
              refine ⟨8483396210259874681708631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22622389894026332484556349 8483396210259874681708631)
              ·
                refine ⟨12725094315389812022562947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8483396210259874681708631 12725094315389812022562947)
                ·
                  refine ⟨19087641473084718033844421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12725094315389812022562947 19087641473084718033844421)
                  ·
                    refine ⟨3578932776203384631345829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19087641473084718033844421 3578932776203384631345829)
                    ·
                      refine ⟨671049895538134618377343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3578932776203384631345829 671049895538134618377343)
                      ·
                        rfl

theorem cell23_1306865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1306865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306865 prefixEnd_1306865 := by exact prefixLift 1306865
  have htrace : WordTrace (prefixWord ++ tailWord_1306865) baseStart_1306865 baseEnd_1306865 := by
    simpa [prefixWord, tailWord_1306865, baseEnd_1306865] using wordTrace_append hprefix tailTrace_1306865
  have hstable : (prefixWord ++ tailWord_1306865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306865).length < 2 ^ (prefixWord ++ tailWord_1306865).sum := by decide
  have hdescent : baseEnd_1306865 < baseStart_1306865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306903 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 2, 2, 2]
def baseStart_1306903 : Nat := 118140960795 + 1306903 * 2 ^ 59
def prefixEnd_1306903 : Nat := 4983230072969 + 3 ^ 40 * 1306903 * 2
def baseEnd_1306903 : Nat := 671069407803005469702169

theorem tailTrace_1306903 : CollatzResearch.WordTrace tailWord_1306903 prefixEnd_1306903 671069407803005469702169 := by
  unfold tailWord_1306903
  simp only [CollatzResearch.WordTrace]
  refine ⟨47666668384321107107549363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31777778922880738071699575 47666668384321107107549363)
  ·
    refine ⟨71500002576481660661324045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47666668384321107107549363 71500002576481660661324045)
    ·
      refine ⟨26812500966180622747996517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71500002576481660661324045 26812500966180622747996517)
      ·
        refine ⟨5027343931158866765249347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26812500966180622747996517 5027343931158866765249347)
        ·
          refine ⟨7541015896738300147874021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027343931158866765249347 7541015896738300147874021)
          ·
            refine ⟨1413940480638431277726379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7541015896738300147874021 1413940480638431277726379)
            ·
              refine ⟨2120910720957646916589569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413940480638431277726379 2120910720957646916589569)
              ·
                refine ⟨1590683040718235187442177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120910720957646916589569 1590683040718235187442177)
                ·
                  refine ⟨1193012280538676390581633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590683040718235187442177 1193012280538676390581633)
                  ·
                    refine ⟨894759210404007292936225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193012280538676390581633 894759210404007292936225)
                    ·
                      refine ⟨671069407803005469702169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894759210404007292936225 671069407803005469702169)
                      ·
                        rfl

theorem cell23_1306903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_1306903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306903 prefixEnd_1306903 := by exact prefixLift 1306903
  have htrace : WordTrace (prefixWord ++ tailWord_1306903) baseStart_1306903 baseEnd_1306903 := by
    simpa [prefixWord, tailWord_1306903, baseEnd_1306903] using wordTrace_append hprefix tailTrace_1306903
  have hstable : (prefixWord ++ tailWord_1306903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306903).length < 2 ^ (prefixWord ++ tailWord_1306903).sum := by decide
  have hdescent : baseEnd_1306903 < baseStart_1306903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306909 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 7]
def baseStart_1306909 : Nat := 118140960795 + 1306909 * 2 ^ 59
def prefixEnd_1306909 : Nat := 4983230072969 + 3 ^ 40 * 1306909 * 2
def baseEnd_1306909 : Nat := 74563609854103605136349

theorem tailTrace_1306909 : CollatzResearch.WordTrace tailWord_1306909 prefixEnd_1306909 74563609854103605136349 := by
  unfold tailWord_1306909
  simp only [CollatzResearch.WordTrace]
  refine ⟨47666887222299370132267781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31777924814866246754845187 47666887222299370132267781)
  ·
    refine ⟨8937541354181131899800209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47666887222299370132267781 8937541354181131899800209)
    ·
      refine ⟨6703156015635848924850157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8937541354181131899800209 6703156015635848924850157)
      ·
        refine ⟨2513683505863443346818809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6703156015635848924850157 2513683505863443346818809)
        ·
          refine ⟨1885262629397582510114107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2513683505863443346818809 1885262629397582510114107)
          ·
            refine ⟨2827893944096373765171161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885262629397582510114107 2827893944096373765171161)
            ·
              refine ⟨2120920458072280323878371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827893944096373765171161 2120920458072280323878371)
              ·
                refine ⟨3181380687108420485817557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120920458072280323878371 3181380687108420485817557)
                ·
                  refine ⟨74563609854103605136349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3181380687108420485817557 74563609854103605136349)
                  ·
                    rfl

theorem cell23_1306909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_1306909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306909 prefixEnd_1306909 := by exact prefixLift 1306909
  have htrace : WordTrace (prefixWord ++ tailWord_1306909) baseStart_1306909 baseEnd_1306909 := by
    simpa [prefixWord, tailWord_1306909, baseEnd_1306909] using wordTrace_append hprefix tailTrace_1306909
  have hstable : (prefixWord ++ tailWord_1306909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306909).length < 2 ^ (prefixWord ++ tailWord_1306909).sum := by decide
  have hdescent : baseEnd_1306909 < baseStart_1306909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306915 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1306915 : Nat := 118140960795 + 1306915 * 2 ^ 59
def prefixEnd_1306915 : Nat := 4983230072969 + 3 ^ 40 * 1306915 * 2
def baseEnd_1306915 : Nat := 671075569570859422752113

theorem tailTrace_1306915 : CollatzResearch.WordTrace tailWord_1306915 prefixEnd_1306915 671075569570859422752113 := by
  unfold tailWord_1306915
  simp only [CollatzResearch.WordTrace]
  refine ⟨47667106060277633156986199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31778070706851755437990799 47667106060277633156986199)
  ·
    refine ⟨71500659090416449735479299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47667106060277633156986199 71500659090416449735479299)
    ·
      refine ⟨107250988635624674603218949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71500659090416449735479299 107250988635624674603218949)
      ·
        refine ⟨20109560369179626488103553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107250988635624674603218949 20109560369179626488103553)
        ·
          refine ⟨15082170276884719866077665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20109560369179626488103553 15082170276884719866077665)
          ·
            refine ⟨11311627707663539899558249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15082170276884719866077665 11311627707663539899558249)
            ·
              refine ⟨8483720780747654924668687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11311627707663539899558249 8483720780747654924668687)
              ·
                refine ⟨12725581171121482387003031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8483720780747654924668687 12725581171121482387003031)
                ·
                  refine ⟨19088371756682223580504547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12725581171121482387003031 19088371756682223580504547)
                  ·
                    refine ⟨28632557635023335370756821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19088371756682223580504547 28632557635023335370756821)
                    ·
                      refine ⟨671075569570859422752113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28632557635023335370756821 671075569570859422752113)
                      ·
                        rfl

theorem cell23_1306915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1306915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306915 prefixEnd_1306915 := by exact prefixLift 1306915
  have htrace : WordTrace (prefixWord ++ tailWord_1306915) baseStart_1306915 baseEnd_1306915 := by
    simpa [prefixWord, tailWord_1306915, baseEnd_1306915] using wordTrace_append hprefix tailTrace_1306915
  have hstable : (prefixWord ++ tailWord_1306915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306915).length < 2 ^ (prefixWord ++ tailWord_1306915).sum := by decide
  have hdescent : baseEnd_1306915 < baseStart_1306915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306920 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_1306920 : Nat := 118140960795 + 1306920 * 2 ^ 59
def prefixEnd_1306920 : Nat := 4983230072969 + 3 ^ 40 * 1306920 * 2
def baseEnd_1306920 : Nat := 671078136974131903189591

theorem tailTrace_1306920 : CollatzResearch.WordTrace tailWord_1306920 prefixEnd_1306920 671078136974131903189591 := by
  unfold tailWord_1306920
  simp only [CollatzResearch.WordTrace]
  refine ⟨23833644212629759505459107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31778192283506346007278809 23833644212629759505459107)
  ·
    refine ⟨35750466318944639258188661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23833644212629759505459107 35750466318944639258188661)
    ·
      refine ⟨3351606217401059930455187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35750466318944639258188661 3351606217401059930455187)
      ·
        refine ⟨5027409326101589895682781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351606217401059930455187 5027409326101589895682781)
        ·
          refine ⟨1885278497288096210881043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5027409326101589895682781 1885278497288096210881043)
          ·
            refine ⟨2827917745932144316321565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885278497288096210881043 2827917745932144316321565)
            ·
              refine ⟨1060469154724554118620587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2827917745932144316321565 1060469154724554118620587)
              ·
                refine ⟨1590703732086831177930881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060469154724554118620587 1590703732086831177930881)
                ·
                  refine ⟨1193027799065123383448161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590703732086831177930881 1193027799065123383448161)
                  ·
                    refine ⟨894770849298842537586121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193027799065123383448161 894770849298842537586121)
                    ·
                      refine ⟨671078136974131903189591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894770849298842537586121 671078136974131903189591)
                      ·
                        rfl

theorem cell23_1306920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_1306920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306920 prefixEnd_1306920 := by exact prefixLift 1306920
  have htrace : WordTrace (prefixWord ++ tailWord_1306920) baseStart_1306920 baseEnd_1306920 := by
    simpa [prefixWord, tailWord_1306920, baseEnd_1306920] using wordTrace_append hprefix tailTrace_1306920
  have hstable : (prefixWord ++ tailWord_1306920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306920).length < 2 ^ (prefixWord ++ tailWord_1306920).sum := by decide
  have hdescent : baseEnd_1306920 < baseStart_1306920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306952 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 5, 4]
def baseStart_1306952 : Nat := 118140960795 + 1306952 * 2 ^ 59
def prefixEnd_1306952 : Nat := 4983230072969 + 3 ^ 40 * 1306952 * 2
def baseEnd_1306952 : Nat := 223698189451691925996481

theorem tailTrace_1306952 : CollatzResearch.WordTrace tailWord_1306952 prefixEnd_1306952 223698189451691925996481 := by
  unfold tailWord_1306952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23834227780571794238041555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31778970374095725650722073 23834227780571794238041555)
  ·
    refine ⟨35751341670857691357062333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23834227780571794238041555 35751341670857691357062333)
    ·
      refine ⟨13406753126571634258898375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35751341670857691357062333 13406753126571634258898375)
      ·
        refine ⟨20110129689857451388347563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13406753126571634258898375 20110129689857451388347563)
        ·
          refine ⟨30165194534786177082521345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20110129689857451388347563 30165194534786177082521345)
          ·
            refine ⟨22623895901089632811891009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30165194534786177082521345 22623895901089632811891009)
            ·
              refine ⟨16967921925817224608918257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22623895901089632811891009 16967921925817224608918257)
              ·
                refine ⟨12725941444362918456688693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16967921925817224608918257 12725941444362918456688693)
                ·
                  refine ⟨1193057010409023605314565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12725941444362918456688693 1193057010409023605314565)
                  ·
                    refine ⟨223698189451691925996481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1193057010409023605314565 223698189451691925996481)
                    ·
                      rfl

theorem cell23_1306952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_1306952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306952 prefixEnd_1306952 := by exact prefixLift 1306952
  have htrace : WordTrace (prefixWord ++ tailWord_1306952) baseStart_1306952 baseEnd_1306952 := by
    simpa [prefixWord, tailWord_1306952, baseEnd_1306952] using wordTrace_append hprefix tailTrace_1306952
  have hstable : (prefixWord ++ tailWord_1306952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306952).length < 2 ^ (prefixWord ++ tailWord_1306952).sum := by decide
  have hdescent : baseEnd_1306952 < baseStart_1306952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306955 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_1306955 : Nat := 118140960795 + 1306955 * 2 ^ 59
def prefixEnd_1306955 : Nat := 4983230072969 + 3 ^ 40 * 1306955 * 2
def baseEnd_1306955 : Nat := 671096108797039266251929

theorem tailTrace_1306955 : CollatzResearch.WordTrace tailWord_1306955 prefixEnd_1306955 671096108797039266251929 := by
  unfold tailWord_1306955
  simp only [CollatzResearch.WordTrace]
  refine ⟨47668564980132719988442319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31779043320088479992294879 47668564980132719988442319)
  ·
    refine ⟨71502847470199079982663479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47668564980132719988442319 71502847470199079982663479)
    ·
      refine ⟨107254271205298619973995219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71502847470199079982663479 107254271205298619973995219)
      ·
        refine ⟨160881406807947929960992829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107254271205298619973995219 160881406807947929960992829)
        ·
          refine ⟨60330527552980473735372311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160881406807947929960992829 60330527552980473735372311)
          ·
            refine ⟨90495791329470710603058467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60330527552980473735372311 90495791329470710603058467)
            ·
              refine ⟨135743686994206065904587701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90495791329470710603058467 135743686994206065904587701)
              ·
                refine ⟨12725970655706818678555097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135743686994206065904587701 12725970655706818678555097)
                ·
                  refine ⟨9544477991780114008916323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12725970655706818678555097 9544477991780114008916323)
                  ·
                    refine ⟨14316716987670171013374485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9544477991780114008916323 14316716987670171013374485)
                    ·
                      refine ⟨671096108797039266251929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14316716987670171013374485 671096108797039266251929)
                      ·
                        rfl

theorem cell23_1306955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_1306955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306955 prefixEnd_1306955 := by exact prefixLift 1306955
  have htrace : WordTrace (prefixWord ++ tailWord_1306955) baseStart_1306955 baseEnd_1306955 := by
    simpa [prefixWord, tailWord_1306955, baseEnd_1306955] using wordTrace_append hprefix tailTrace_1306955
  have hstable : (prefixWord ++ tailWord_1306955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306955).length < 2 ^ (prefixWord ++ tailWord_1306955).sum := by decide
  have hdescent : baseEnd_1306955 < baseStart_1306955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306995 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 9]
def baseStart_1306995 : Nat := 118140960795 + 1306995 * 2 ^ 59
def prefixEnd_1306995 : Nat := 4983230072969 + 3 ^ 40 * 1306995 * 2
def baseEnd_1306995 : Nat := 223705549341073036583915

theorem tailTrace_1306995 : CollatzResearch.WordTrace tailWord_1306995 prefixEnd_1306995 223705549341073036583915 := by
  unfold tailWord_1306995
  simp only [CollatzResearch.WordTrace]
  refine ⟨47670023899987806819898439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31780015933325204546598959 47670023899987806819898439)
  ·
    refine ⟨71505035849981710229847659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47670023899987806819898439 71505035849981710229847659)
    ·
      refine ⟨107257553774972565344771489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71505035849981710229847659 107257553774972565344771489)
      ·
        refine ⟨80443165331229424008578617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107257553774972565344771489 80443165331229424008578617)
        ·
          refine ⟨60332373998422068006433963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80443165331229424008578617 60332373998422068006433963)
          ·
            refine ⟨90498560997633102009650945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60332373998422068006433963 90498560997633102009650945)
            ·
              refine ⟨67873920748224826507238209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90498560997633102009650945 67873920748224826507238209)
              ·
                refine ⟨50905440561168619880428657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67873920748224826507238209 50905440561168619880428657)
                ·
                  refine ⟨38179080420876464910321493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50905440561168619880428657 38179080420876464910321493)
                  ·
                    refine ⟨223705549341073036583915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38179080420876464910321493 223705549341073036583915)
                    ·
                      rfl

theorem cell23_1306995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_1306995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1306995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1306995 prefixEnd_1306995 := by exact prefixLift 1306995
  have htrace : WordTrace (prefixWord ++ tailWord_1306995) baseStart_1306995 baseEnd_1306995 := by
    simpa [prefixWord, tailWord_1306995, baseEnd_1306995] using wordTrace_append hprefix tailTrace_1306995
  have hstable : (prefixWord ++ tailWord_1306995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306995).length < 2 ^ (prefixWord ++ tailWord_1306995).sum := by decide
  have hdescent : baseEnd_1306995 < baseStart_1306995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307053 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1307053 : Nat := 118140960795 + 1307053 * 2 ^ 59
def prefixEnd_1307053 : Nat := 4983230072969 + 3 ^ 40 * 1307053 * 2
def baseEnd_1307053 : Nat := 671146429901179882826479

theorem tailTrace_1307053 : CollatzResearch.WordTrace tailWord_1307053 prefixEnd_1307053 671146429901179882826479 := by
  unfold tailWord_1307053
  simp only [CollatzResearch.WordTrace]
  refine ⟨47672139333777682725509813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31781426222518455150339875 47672139333777682725509813)
  ·
    refine ⟨4469263062541657755516545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47672139333777682725509813 4469263062541657755516545)
    ·
      refine ⟨3351947296906243316637409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4469263062541657755516545 3351947296906243316637409)
      ·
        refine ⟨2513960472679682487478057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3351947296906243316637409 2513960472679682487478057)
        ·
          refine ⟨1885470354509761865608543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2513960472679682487478057 1885470354509761865608543)
          ·
            refine ⟨2828205531764642798412815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885470354509761865608543 2828205531764642798412815)
            ·
              refine ⟨4242308297646964197619223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828205531764642798412815 4242308297646964197619223)
              ·
                refine ⟨6363462446470446296428835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242308297646964197619223 6363462446470446296428835)
                ·
                  refine ⟨9545193669705669444643253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6363462446470446296428835 9545193669705669444643253)
                  ·
                    refine ⟨894861906534906510435305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9545193669705669444643253 894861906534906510435305)
                    ·
                      refine ⟨671146429901179882826479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894861906534906510435305 671146429901179882826479)
                      ·
                        rfl

theorem cell23_1307053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1307053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307053 prefixEnd_1307053 := by exact prefixLift 1307053
  have htrace : WordTrace (prefixWord ++ tailWord_1307053) baseStart_1307053 baseEnd_1307053 := by
    simpa [prefixWord, tailWord_1307053, baseEnd_1307053] using wordTrace_append hprefix tailTrace_1307053
  have hstable : (prefixWord ++ tailWord_1307053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307053).length < 2 ^ (prefixWord ++ tailWord_1307053).sum := by decide
  have hdescent : baseEnd_1307053 < baseStart_1307053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307093 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1307093 : Nat := 118140960795 + 1307093 * 2 ^ 59
def prefixEnd_1307093 : Nat := 4983230072969 + 3 ^ 40 * 1307093 * 2
def baseEnd_1307093 : Nat := 223722323042453242108765

theorem tailTrace_1307093 : CollatzResearch.WordTrace tailWord_1307093 prefixEnd_1307093 223722323042453242108765 := by
  unfold tailWord_1307093
  simp only [CollatzResearch.WordTrace]
  refine ⟨47673598253632769556965933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31782398835755179704643955 47673598253632769556965933)
  ·
    refine ⟨17877599345112288583862225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47673598253632769556965933 17877599345112288583862225)
    ·
      refine ⟨13408199508834216437896669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17877599345112288583862225 13408199508834216437896669)
      ·
        refine ⟨5028074815812831164211251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13408199508834216437896669 5028074815812831164211251)
        ·
          refine ⟨7542112223719246746316877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028074815812831164211251 7542112223719246746316877)
          ·
            refine ⟨2828292083894717529868829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7542112223719246746316877 2828292083894717529868829)
            ·
              refine ⟨1060609531460519073700811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2828292083894717529868829 1060609531460519073700811)
              ·
                refine ⟨1590914297190778610551217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060609531460519073700811 1590914297190778610551217)
                ·
                  refine ⟨1193185722893083957913413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590914297190778610551217 1193185722893083957913413)
                  ·
                    refine ⟨223722323042453242108765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1193185722893083957913413 223722323042453242108765)
                    ·
                      rfl

theorem cell23_1307093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1307093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307093 prefixEnd_1307093 := by exact prefixLift 1307093
  have htrace : WordTrace (prefixWord ++ tailWord_1307093) baseStart_1307093 baseEnd_1307093 := by
    simpa [prefixWord, tailWord_1307093, baseEnd_1307093] using wordTrace_append hprefix tailTrace_1307093
  have hstable : (prefixWord ++ tailWord_1307093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307093).length < 2 ^ (prefixWord ++ tailWord_1307093).sum := by decide
  have hdescent : baseEnd_1307093 < baseStart_1307093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307117 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1307117 : Nat := 118140960795 + 1307117 * 2 ^ 59
def prefixEnd_1307117 : Nat := 4983230072969 + 3 ^ 40 * 1307117 * 2
def baseEnd_1307117 : Nat := 671179292663067632426185

theorem tailTrace_1307117 : CollatzResearch.WordTrace tailWord_1307117 prefixEnd_1307117 671179292663067632426185 := by
  unfold tailWord_1307117
  simp only [CollatzResearch.WordTrace]
  refine ⟨47674473605545821655839605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31782982403697214437226403 47674473605545821655839605)
  ·
    refine ⟨4469481900519920780234963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47674473605545821655839605 4469481900519920780234963)
    ·
      refine ⟨6704222850779881170352445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469481900519920780234963 6704222850779881170352445)
      ·
        refine ⟨2514083569042455438882167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6704222850779881170352445 2514083569042455438882167)
        ·
          refine ⟨3771125353563683158323251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514083569042455438882167 3771125353563683158323251)
          ·
            refine ⟨5656688030345524737484877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771125353563683158323251 5656688030345524737484877)
            ·
              refine ⟨2121258011379571776556829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5656688030345524737484877 2121258011379571776556829)
              ·
                refine ⟨795471754267339416208811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2121258011379571776556829 795471754267339416208811)
                ·
                  refine ⟨1193207631401009124313217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795471754267339416208811 1193207631401009124313217)
                  ·
                    refine ⟨894905723550756843234913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193207631401009124313217 894905723550756843234913)
                    ·
                      refine ⟨671179292663067632426185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894905723550756843234913 671179292663067632426185)
                      ·
                        rfl

theorem cell23_1307117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1307117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307117 prefixEnd_1307117 := by exact prefixLift 1307117
  have htrace : WordTrace (prefixWord ++ tailWord_1307117) baseStart_1307117 baseEnd_1307117 := by
    simpa [prefixWord, tailWord_1307117, baseEnd_1307117] using wordTrace_append hprefix tailTrace_1307117
  have hstable : (prefixWord ++ tailWord_1307117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307117).length < 2 ^ (prefixWord ++ tailWord_1307117).sum := by decide
  have hdescent : baseEnd_1307117 < baseStart_1307117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307150 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1307150 : Nat := 118140960795 + 1307150 * 2 ^ 59
def prefixEnd_1307150 : Nat := 4983230072969 + 3 ^ 40 * 1307150 * 2
def baseEnd_1307150 : Nat := 671196237524666003313533

theorem tailTrace_1307150 : CollatzResearch.WordTrace tailWord_1307150 prefixEnd_1307150 671196237524666003313533 := by
  unfold tailWord_1307150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5959459651803283536473863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31783784809617512194527269 5959459651803283536473863)
  ·
    refine ⟨8939189477704925304710795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5959459651803283536473863 8939189477704925304710795)
    ·
      refine ⟨13408784216557387957066193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8939189477704925304710795 13408784216557387957066193)
      ·
        refine ⟨10056588162418040967799645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13408784216557387957066193 10056588162418040967799645)
        ·
          refine ⟨3771220560906765362924867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10056588162418040967799645 3771220560906765362924867)
          ·
            refine ⟨5656830841360148044387301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771220560906765362924867 5656830841360148044387301)
            ·
              refine ⟨1060655782755027758322619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5656830841360148044387301 1060655782755027758322619)
              ·
                refine ⟨1590983674132541637483929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060655782755027758322619 1590983674132541637483929)
                ·
                  refine ⟨1193237755599406228112947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590983674132541637483929 1193237755599406228112947)
                  ·
                    refine ⟨1789856633399109342169421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1193237755599406228112947 1789856633399109342169421)
                    ·
                      refine ⟨671196237524666003313533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1789856633399109342169421 671196237524666003313533)
                      ·
                        rfl

theorem cell23_1307150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1307150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307150 prefixEnd_1307150 := by exact prefixLift 1307150
  have htrace : WordTrace (prefixWord ++ tailWord_1307150) baseStart_1307150 baseEnd_1307150 := by
    simpa [prefixWord, tailWord_1307150, baseEnd_1307150] using wordTrace_append hprefix tailTrace_1307150
  have hstable : (prefixWord ++ tailWord_1307150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307150).length < 2 ^ (prefixWord ++ tailWord_1307150).sum := by decide
  have hdescent : baseEnd_1307150 < baseStart_1307150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307160 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 1, 3, 2]
def baseStart_1307160 : Nat := 118140960795 + 1307160 * 2 ^ 59
def prefixEnd_1307160 : Nat := 4983230072969 + 3 ^ 40 * 1307160 * 2
def baseEnd_1307160 : Nat := 671201372331210964188487

theorem tailTrace_1307160 : CollatzResearch.WordTrace tailWord_1307160 prefixEnd_1307160 671201372331210964188487 := by
  unfold tailWord_1307160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23838020972195019999827467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31784027962926693333103289 23838020972195019999827467)
  ·
    refine ⟨35757031458292529999741201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23838020972195019999827467 35757031458292529999741201)
    ·
      refine ⟨26817773593719397499805901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35757031458292529999741201 26817773593719397499805901)
      ·
        refine ⟨10056665097644774062427213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26817773593719397499805901 10056665097644774062427213)
        ·
          refine ⟨3771249411616790273410205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10056665097644774062427213 3771249411616790273410205)
          ·
            refine ⟨1414218529356296352528827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3771249411616790273410205 1414218529356296352528827)
            ·
              refine ⟨2121327794034444528793241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414218529356296352528827 2121327794034444528793241)
              ·
                refine ⟨1590995845525833396594931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121327794034444528793241 1590995845525833396594931)
                ·
                  refine ⟨2386493768288750094892397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590995845525833396594931 2386493768288750094892397)
                  ·
                    refine ⟨894935163108281285584649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386493768288750094892397 894935163108281285584649)
                    ·
                      refine ⟨671201372331210964188487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 894935163108281285584649 671201372331210964188487)
                      ·
                        rfl

theorem cell23_1307160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_1307160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307160 prefixEnd_1307160 := by exact prefixLift 1307160
  have htrace : WordTrace (prefixWord ++ tailWord_1307160) baseStart_1307160 baseEnd_1307160 := by
    simpa [prefixWord, tailWord_1307160, baseEnd_1307160] using wordTrace_append hprefix tailTrace_1307160
  have hstable : (prefixWord ++ tailWord_1307160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307160).length < 2 ^ (prefixWord ++ tailWord_1307160).sum := by decide
  have hdescent : baseEnd_1307160 < baseStart_1307160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307176 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1307176 : Nat := 118140960795 + 1307176 * 2 ^ 59
def prefixEnd_1307176 : Nat := 4983230072969 + 3 ^ 40 * 1307176 * 2
def baseEnd_1307176 : Nat := 671209588021682901588413

theorem tailTrace_1307176 : CollatzResearch.WordTrace tailWord_1307176 prefixEnd_1307176 671209588021682901588413 := by
  unfold tailWord_1307176
  simp only [CollatzResearch.WordTrace]
  refine ⟨23838312756166037366118691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31784417008221383154824921 23838312756166037366118691)
  ·
    refine ⟨35757469134249056049178037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23838312756166037366118691 35757469134249056049178037)
    ·
      refine ⟨3352262731335849004610441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35757469134249056049178037 3352262731335849004610441)
      ·
        refine ⟨2514197048501886753457831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3352262731335849004610441 2514197048501886753457831)
        ·
          refine ⟨3771295572752830130186747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514197048501886753457831 3771295572752830130186747)
          ·
            refine ⟨5656943359129245195280121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771295572752830130186747 5656943359129245195280121)
            ·
              refine ⟨4242707519346933896460091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5656943359129245195280121 4242707519346933896460091)
              ·
                refine ⟨6364061279020400844690137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242707519346933896460091 6364061279020400844690137)
                ·
                  refine ⟨4773045959265300633517603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6364061279020400844690137 4773045959265300633517603)
                  ·
                    refine ⟨7159568938897950950276405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4773045959265300633517603 7159568938897950950276405)
                    ·
                      refine ⟨671209588021682901588413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7159568938897950950276405 671209588021682901588413)
                      ·
                        rfl

theorem cell23_1307176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1307176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307176 prefixEnd_1307176 := by exact prefixLift 1307176
  have htrace : WordTrace (prefixWord ++ tailWord_1307176) baseStart_1307176 baseEnd_1307176 := by
    simpa [prefixWord, tailWord_1307176, baseEnd_1307176] using wordTrace_append hprefix tailTrace_1307176
  have hstable : (prefixWord ++ tailWord_1307176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307176).length < 2 ^ (prefixWord ++ tailWord_1307176).sum := by decide
  have hdescent : baseEnd_1307176 < baseStart_1307176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307334 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1307334 : Nat := 118140960795 + 1307334 * 2 ^ 59
def prefixEnd_1307334 : Nat := 4983230072969 + 3 ^ 40 * 1307334 * 2
def baseEnd_1307334 : Nat := 671290717965093283412687

theorem tailTrace_1307334 : CollatzResearch.WordTrace tailWord_1307334 prefixEnd_1307334 671290717965093283412687 := by
  unfold tailWord_1307334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490074632679989616140283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31788258830506445144326037 1490074632679989616140283)
  ·
    refine ⟨2235111949019984424210425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490074632679989616140283 2235111949019984424210425)
    ·
      refine ⟨1676333961764988318157819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2235111949019984424210425 1676333961764988318157819)
      ·
        refine ⟨2514500942647482477236729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676333961764988318157819 2514500942647482477236729)
        ·
          refine ⟨1885875706985611857927547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2514500942647482477236729 1885875706985611857927547)
          ·
            refine ⟨2828813560478417786891321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885875706985611857927547 2828813560478417786891321)
            ·
              refine ⟨2121610170358813340168491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2828813560478417786891321 2121610170358813340168491)
              ·
                refine ⟨3182415255538220010252737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121610170358813340168491 3182415255538220010252737)
                ·
                  refine ⟨2386811441653665007689553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3182415255538220010252737 2386811441653665007689553)
                  ·
                    refine ⟨1790108581240248755767165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2386811441653665007689553 1790108581240248755767165)
                    ·
                      refine ⟨671290717965093283412687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790108581240248755767165 671290717965093283412687)
                      ·
                        rfl

theorem cell23_1307334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1307334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307334 prefixEnd_1307334 := by exact prefixLift 1307334
  have htrace : WordTrace (prefixWord ++ tailWord_1307334) baseStart_1307334 baseEnd_1307334 := by
    simpa [prefixWord, tailWord_1307334, baseEnd_1307334] using wordTrace_append hprefix tailTrace_1307334
  have hstable : (prefixWord ++ tailWord_1307334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307334).length < 2 ^ (prefixWord ++ tailWord_1307334).sum := by decide
  have hdescent : baseEnd_1307334 < baseStart_1307334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307339 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_1307339 : Nat := 118140960795 + 1307339 * 2 ^ 59
def prefixEnd_1307339 : Nat := 4983230072969 + 3 ^ 40 * 1307339 * 2
def baseEnd_1307339 : Nat := 671293285368365763850163

theorem tailTrace_1307339 : CollatzResearch.WordTrace tailWord_1307339 prefixEnd_1307339 671293285368365763850163 := by
  unfold tailWord_1307339
  simp only [CollatzResearch.WordTrace]
  refine ⟨47682570610741553570421071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31788380407161035713614047 47682570610741553570421071)
  ·
    refine ⟨71523855916112330355631607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47682570610741553570421071 71523855916112330355631607)
    ·
      refine ⟨107285783874168495533447411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71523855916112330355631607 107285783874168495533447411)
      ·
        refine ⟨160928675811252743300171117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107285783874168495533447411 160928675811252743300171117)
        ·
          refine ⟨60348253429219778737564169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160928675811252743300171117 60348253429219778737564169)
          ·
            refine ⟨45261190071914834053173127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60348253429219778737564169 45261190071914834053173127)
            ·
              refine ⟨67891785107872251079759691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45261190071914834053173127 67891785107872251079759691)
              ·
                refine ⟨101837677661808376619639537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67891785107872251079759691 101837677661808376619639537)
                ·
                  refine ⟨76378258246356282464729653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101837677661808376619639537 76378258246356282464729653)
                  ·
                    refine ⟨7160461710595901481068405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76378258246356282464729653 7160461710595901481068405)
                    ·
                      refine ⟨671293285368365763850163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7160461710595901481068405 671293285368365763850163)
                      ·
                        rfl

theorem cell23_1307339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_1307339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307339 prefixEnd_1307339 := by exact prefixLift 1307339
  have htrace : WordTrace (prefixWord ++ tailWord_1307339) baseStart_1307339 baseEnd_1307339 := by
    simpa [prefixWord, tailWord_1307339, baseEnd_1307339] using wordTrace_append hprefix tailTrace_1307339
  have hstable : (prefixWord ++ tailWord_1307339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307339).length < 2 ^ (prefixWord ++ tailWord_1307339).sum := by decide
  have hdescent : baseEnd_1307339 < baseStart_1307339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307340 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1307340 : Nat := 118140960795 + 1307340 * 2 ^ 59
def prefixEnd_1307340 : Nat := 4983230072969 + 3 ^ 40 * 1307340 * 2
def baseEnd_1307340 : Nat := 671293798849020259937659

theorem tailTrace_1307340 : CollatzResearch.WordTrace tailWord_1307340 prefixEnd_1307340 671293798849020259937659 := by
  unfold tailWord_1307340
  simp only [CollatzResearch.WordTrace]
  refine ⟨23841303541868965370603737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31788404722491953827471649 23841303541868965370603737)
  ·
    refine ⟨17880977656401724027952803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23841303541868965370603737 17880977656401724027952803)
    ·
      refine ⟨26821466484602586041929205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17880977656401724027952803 26821466484602586041929205)
      ·
        refine ⟨2514512482931492441430863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26821466484602586041929205 2514512482931492441430863)
        ·
          refine ⟨3771768724397238662146295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514512482931492441430863 3771768724397238662146295)
          ·
            refine ⟨5657653086595857993219443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771768724397238662146295 5657653086595857993219443)
            ·
              refine ⟨8486479629893786989829165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657653086595857993219443 8486479629893786989829165)
              ·
                refine ⟨3182429861210170121185937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8486479629893786989829165 3182429861210170121185937)
                ·
                  refine ⟨2386822395907627590889453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3182429861210170121185937 2386822395907627590889453)
                  ·
                    refine ⟨895058398465360346583545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386822395907627590889453 895058398465360346583545)
                    ·
                      refine ⟨671293798849020259937659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895058398465360346583545 671293798849020259937659)
                      ·
                        rfl

theorem cell23_1307340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1307340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307340 prefixEnd_1307340 := by exact prefixLift 1307340
  have htrace : WordTrace (prefixWord ++ tailWord_1307340) baseStart_1307340 baseEnd_1307340 := by
    simpa [prefixWord, tailWord_1307340, baseEnd_1307340] using wordTrace_append hprefix tailTrace_1307340
  have hstable : (prefixWord ++ tailWord_1307340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307340).length < 2 ^ (prefixWord ++ tailWord_1307340).sum := by decide
  have hdescent : baseEnd_1307340 < baseStart_1307340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307359 : List Nat := [1, 1, 2, 3, 2, 14]
def baseStart_1307359 : Nat := 118140960795 + 1307359 * 2 ^ 59
def prefixEnd_1307359 : Nat := 4983230072969 + 3 ^ 40 * 1307359 * 2
def baseEnd_1307359 : Nat := 2762566069882533685597

theorem tailTrace_1307359 : CollatzResearch.WordTrace tailWord_1307359 prefixEnd_1307359 2762566069882533685597 := by
  unfold tailWord_1307359
  simp only [CollatzResearch.WordTrace]
  refine ⟨47683300070669096986149131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31788866713779397990766087 47683300070669096986149131)
  ·
    refine ⟨71524950106003645479223697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47683300070669096986149131 71524950106003645479223697)
    ·
      refine ⟨53643712579502734109417773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71524950106003645479223697 53643712579502734109417773)
      ·
        refine ⟨20116392217313525291031665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53643712579502734109417773 20116392217313525291031665)
        ·
          refine ⟨15087294162985143968273749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20116392217313525291031665 15087294162985143968273749)
          ·
            refine ⟨2762566069882533685597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 15087294162985143968273749 2762566069882533685597)
            ·
              rfl

theorem cell23_1307359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 14].length) (baseStart_1307359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307359 prefixEnd_1307359 := by exact prefixLift 1307359
  have htrace : WordTrace (prefixWord ++ tailWord_1307359) baseStart_1307359 baseEnd_1307359 := by
    simpa [prefixWord, tailWord_1307359, baseEnd_1307359] using wordTrace_append hprefix tailTrace_1307359
  have hstable : (prefixWord ++ tailWord_1307359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307359).length < 2 ^ (prefixWord ++ tailWord_1307359).sum := by decide
  have hdescent : baseEnd_1307359 < baseStart_1307359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307364 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_1307364 : Nat := 118140960795 + 1307364 * 2 ^ 59
def prefixEnd_1307364 : Nat := 4983230072969 + 3 ^ 40 * 1307364 * 2
def baseEnd_1307364 : Nat := 671306122384728166037549

theorem tailTrace_1307364 : CollatzResearch.WordTrace tailWord_1307364 prefixEnd_1307364 671306122384728166037549 := by
  unfold tailWord_1307364
  simp only [CollatzResearch.WordTrace]
  refine ⟨23841741217825491420040573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31788988290433988560054097 23841741217825491420040573)
  ·
    refine ⟨8940652956684559282515215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23841741217825491420040573 8940652956684559282515215)
    ·
      refine ⟨13410979435026838923772823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8940652956684559282515215 13410979435026838923772823)
      ·
        refine ⟨20116469152540258385659235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13410979435026838923772823 20116469152540258385659235)
        ·
          refine ⟨30174703728810387578488853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20116469152540258385659235 30174703728810387578488853)
          ·
            refine ⟨1414439237287986917741665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30174703728810387578488853 1414439237287986917741665)
            ·
              refine ⟨1060829427965990188306249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414439237287986917741665 1060829427965990188306249)
              ·
                refine ⟨795622070974492641229687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060829427965990188306249 795622070974492641229687)
                ·
                  refine ⟨1193433106461738961844531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795622070974492641229687 1193433106461738961844531)
                  ·
                    refine ⟨1790149659692608442766797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1193433106461738961844531 1790149659692608442766797)
                    ·
                      refine ⟨671306122384728166037549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790149659692608442766797 671306122384728166037549)
                      ·
                        rfl

theorem cell23_1307364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_1307364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307364 prefixEnd_1307364 := by exact prefixLift 1307364
  have htrace : WordTrace (prefixWord ++ tailWord_1307364) baseStart_1307364 baseEnd_1307364 := by
    simpa [prefixWord, tailWord_1307364, baseEnd_1307364] using wordTrace_append hprefix tailTrace_1307364
  have hstable : (prefixWord ++ tailWord_1307364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307364).length < 2 ^ (prefixWord ++ tailWord_1307364).sum := by decide
  have hdescent : baseEnd_1307364 < baseStart_1307364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307370 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_1307370 : Nat := 118140960795 + 1307370 * 2 ^ 59
def prefixEnd_1307370 : Nat := 4983230072969 + 3 ^ 40 * 1307370 * 2
def baseEnd_1307370 : Nat := 671309203268655142562521

theorem tailTrace_1307370 : CollatzResearch.WordTrace tailWord_1307370 prefixEnd_1307370 671309203268655142562521 := by
  unfold tailWord_1307370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11920925318407311466199891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31789134182419497243199709 11920925318407311466199891)
  ·
    refine ⟨17881387977610967199299837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11920925318407311466199891 17881387977610967199299837)
    ·
      refine ⟨6705520491604112699737439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17881387977610967199299837 6705520491604112699737439)
      ·
        refine ⟨10058280737406169049606159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6705520491604112699737439 10058280737406169049606159)
        ·
          refine ⟨15087421106109253574409239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10058280737406169049606159 15087421106109253574409239)
          ·
            refine ⟨22631131659163880361613859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15087421106109253574409239 22631131659163880361613859)
            ·
              refine ⟨33946697488745820542420789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22631131659163880361613859 33946697488745820542420789)
              ·
                refine ⟨3182502889569920675851949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33946697488745820542420789 3182502889569920675851949)
                ·
                  refine ⟨1193438583588720253444481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3182502889569920675851949 1193438583588720253444481)
                  ·
                    refine ⟨895078937691540190083361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193438583588720253444481 895078937691540190083361)
                    ·
                      refine ⟨671309203268655142562521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895078937691540190083361 671309203268655142562521)
                      ·
                        rfl

theorem cell23_1307370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_1307370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307370 prefixEnd_1307370 := by exact prefixLift 1307370
  have htrace : WordTrace (prefixWord ++ tailWord_1307370) baseStart_1307370 baseEnd_1307370 := by
    simpa [prefixWord, tailWord_1307370, baseEnd_1307370] using wordTrace_append hprefix tailTrace_1307370
  have hstable : (prefixWord ++ tailWord_1307370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307370).length < 2 ^ (prefixWord ++ tailWord_1307370).sum := by decide
  have hdescent : baseEnd_1307370 < baseStart_1307370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307373 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1307373 : Nat := 118140960795 + 1307373 * 2 ^ 59
def prefixEnd_1307373 : Nat := 4983230072969 + 3 ^ 40 * 1307373 * 2
def baseEnd_1307373 : Nat := 671310743710618630825007

theorem tailTrace_1307373 : CollatzResearch.WordTrace tailWord_1307373 prefixEnd_1307373 671310743710618630825007 := by
  unfold tailWord_1307373
  simp only [CollatzResearch.WordTrace]
  refine ⟨47683810692618377377158773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31789207128412251584772515 47683810692618377377158773)
  ·
    refine ⟨4470357252432972879108635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47683810692618377377158773 4470357252432972879108635)
    ·
      refine ⟨6705535878649459318662953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4470357252432972879108635 6705535878649459318662953)
      ·
        refine ⟨5029151908987094488997215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6705535878649459318662953 5029151908987094488997215)
        ·
          refine ⟨7543727863480641733495823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5029151908987094488997215 7543727863480641733495823)
          ·
            refine ⟨11315591795220962600243735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7543727863480641733495823 11315591795220962600243735)
            ·
              refine ⟨16973387692831443900365603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11315591795220962600243735 16973387692831443900365603)
              ·
                refine ⟨25460081539247165850548405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16973387692831443900365603 25460081539247165850548405)
                ·
                  refine ⟨2386882644304421798488913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25460081539247165850548405 2386882644304421798488913)
                  ·
                    refine ⟨1790161983228316348866685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2386882644304421798488913 1790161983228316348866685)
                    ·
                      refine ⟨671310743710618630825007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790161983228316348866685 671310743710618630825007)
                      ·
                        rfl

theorem cell23_1307373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1307373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307373 prefixEnd_1307373 := by exact prefixLift 1307373
  have htrace : WordTrace (prefixWord ++ tailWord_1307373) baseStart_1307373 baseEnd_1307373 := by
    simpa [prefixWord, tailWord_1307373, baseEnd_1307373] using wordTrace_append hprefix tailTrace_1307373
  have hstable : (prefixWord ++ tailWord_1307373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307373).length < 2 ^ (prefixWord ++ tailWord_1307373).sum := by decide
  have hdescent : baseEnd_1307373 < baseStart_1307373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307390 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1307390 : Nat := 118140960795 + 1307390 * 2 ^ 59
def prefixEnd_1307390 : Nat := 4983230072969 + 3 ^ 40 * 1307390 * 2
def baseEnd_1307390 : Nat := 671319472881745064312429

theorem tailTrace_1307390 : CollatzResearch.WordTrace tailWord_1307390 prefixEnd_1307390 671319472881745064312429 := by
  unfold tailWord_1307390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5960553841694598660065953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31789620489037859520351749 5960553841694598660065953)
  ·
    refine ⟨4470415381270948995049465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5960553841694598660065953 4470415381270948995049465)
    ·
      refine ⟨3352811535953211746287099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4470415381270948995049465 3352811535953211746287099)
      ·
        refine ⟨5029217303929817619430649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3352811535953211746287099 5029217303929817619430649)
        ·
          refine ⟨3771912977947363214572987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5029217303929817619430649 3771912977947363214572987)
          ·
            refine ⟨5657869466921044821859481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771912977947363214572987 5657869466921044821859481)
            ·
              refine ⟨4243402100190783616394611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5657869466921044821859481 4243402100190783616394611)
              ·
                refine ⟨6365103150286175424591917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4243402100190783616394611 6365103150286175424591917)
                ·
                  refine ⟨2386913681357315784221969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6365103150286175424591917 2386913681357315784221969)
                  ·
                    refine ⟨1790185261017986838166477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2386913681357315784221969 1790185261017986838166477)
                    ·
                      refine ⟨671319472881745064312429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790185261017986838166477 671319472881745064312429)
                      ·
                        rfl

theorem cell23_1307390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1307390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307390 prefixEnd_1307390 := by exact prefixLift 1307390
  have htrace : WordTrace (prefixWord ++ tailWord_1307390) baseStart_1307390 baseEnd_1307390 := by
    simpa [prefixWord, tailWord_1307390, baseEnd_1307390] using wordTrace_append hprefix tailTrace_1307390
  have hstable : (prefixWord ++ tailWord_1307390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307390).length < 2 ^ (prefixWord ++ tailWord_1307390).sum := by decide
  have hdescent : baseEnd_1307390 < baseStart_1307390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307403 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 3]
def baseStart_1307403 : Nat := 118140960795 + 1307403 * 2 ^ 59
def prefixEnd_1307403 : Nat := 4983230072969 + 3 ^ 40 * 1307403 * 2
def baseEnd_1307403 : Nat := 671326148130253513449869

theorem tailTrace_1307403 : CollatzResearch.WordTrace tailWord_1307403 prefixEnd_1307403 671326148130253513449869 := by
  unfold tailWord_1307403
  simp only [CollatzResearch.WordTrace]
  refine ⟨47684904882509692500750863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31789936588339795000500575 47684904882509692500750863)
  ·
    refine ⟨71527357323764538751126295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47684904882509692500750863 71527357323764538751126295)
    ·
      refine ⟨107291035985646808126689443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71527357323764538751126295 107291035985646808126689443)
      ·
        refine ⟨160936553978470212190034165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107291035985646808126689443 160936553978470212190034165)
        ·
          refine ⟨15087801935481582392815703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160936553978470212190034165 15087801935481582392815703)
          ·
            refine ⟨22631702903222373589223555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15087801935481582392815703 22631702903222373589223555)
            ·
              refine ⟨33947554354833560383835333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22631702903222373589223555 33947554354833560383835333)
              ·
                refine ⟨6365166441531292571969125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33947554354833560383835333 6365166441531292571969125)
                ·
                  refine ⟨1193468707787117357244211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6365166441531292571969125 1193468707787117357244211)
                  ·
                    refine ⟨1790203061680676035866317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1193468707787117357244211 1790203061680676035866317)
                    ·
                      refine ⟨671326148130253513449869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790203061680676035866317 671326148130253513449869)
                      ·
                        rfl

theorem cell23_1307403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 1, 3].length) (baseStart_1307403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307403 prefixEnd_1307403 := by exact prefixLift 1307403
  have htrace : WordTrace (prefixWord ++ tailWord_1307403) baseStart_1307403 baseEnd_1307403 := by
    simpa [prefixWord, tailWord_1307403, baseEnd_1307403] using wordTrace_append hprefix tailTrace_1307403
  have hstable : (prefixWord ++ tailWord_1307403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307403).length < 2 ^ (prefixWord ++ tailWord_1307403).sum := by decide
  have hdescent : baseEnd_1307403 < baseStart_1307403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307420 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1307420 : Nat := 118140960795 + 1307420 * 2 ^ 59
def prefixEnd_1307420 : Nat := 4983230072969 + 3 ^ 40 * 1307420 * 2
def baseEnd_1307420 : Nat := 671334877301379946937291

theorem tailTrace_1307420 : CollatzResearch.WordTrace tailWord_1307420 prefixEnd_1307420 671334877301379946937291 := by
  unfold tailWord_1307420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842762461724052202059857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31790349948965402936079809 23842762461724052202059857)
  ·
    refine ⟨17882071846293039151544893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23842762461724052202059857 17882071846293039151544893)
    ·
      refine ⟨6705776942359889681829335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17882071846293039151544893 6705776942359889681829335)
      ·
        refine ⟨10058665413539834522744003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6705776942359889681829335 10058665413539834522744003)
        ·
          refine ⟨15087998120309751784116005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10058665413539834522744003 15087998120309751784116005)
          ·
            refine ⟨2828999647558078459521751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15087998120309751784116005 2828999647558078459521751)
            ·
              refine ⟨4243499471337117689282627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828999647558078459521751 4243499471337117689282627)
              ·
                refine ⟨6365249207005676533923941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4243499471337117689282627 6365249207005676533923941)
                ·
                  refine ⟨1193484226313564350110739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6365249207005676533923941 1193484226313564350110739)
                  ·
                    refine ⟨1790226339470346525166109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1193484226313564350110739 1790226339470346525166109)
                    ·
                      refine ⟨671334877301379946937291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790226339470346525166109 671334877301379946937291)
                      ·
                        rfl

theorem cell23_1307420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1307420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307420 prefixEnd_1307420 := by exact prefixLift 1307420
  have htrace : WordTrace (prefixWord ++ tailWord_1307420) baseStart_1307420 baseEnd_1307420 := by
    simpa [prefixWord, tailWord_1307420, baseEnd_1307420] using wordTrace_append hprefix tailTrace_1307420
  have hstable : (prefixWord ++ tailWord_1307420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307420).length < 2 ^ (prefixWord ++ tailWord_1307420).sum := by decide
  have hdescent : baseEnd_1307420 < baseStart_1307420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307434 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1307434 : Nat := 118140960795 + 1307434 * 2 ^ 59
def prefixEnd_1307434 : Nat := 4983230072969 + 3 ^ 40 * 1307434 * 2
def baseEnd_1307434 : Nat := 671342066030542892162227

theorem tailTrace_1307434 : CollatzResearch.WordTrace tailWord_1307434 prefixEnd_1307434 671342066030542892162227 := by
  unfold tailWord_1307434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11921508886349346198782339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31790690363598256530086237 11921508886349346198782339)
  ·
    refine ⟨17882263329524019298173509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11921508886349346198782339 17882263329524019298173509)
    ·
      refine ⟨3352924374285753618407533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17882263329524019298173509 3352924374285753618407533)
      ·
        refine ⟨1257346640357157606902825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3352924374285753618407533 1257346640357157606902825)
        ·
          refine ⟨943009980267868205177119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257346640357157606902825 943009980267868205177119)
          ·
            refine ⟨1414514970401802307765679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943009980267868205177119 1414514970401802307765679)
            ·
              refine ⟨2121772455602703461648519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414514970401802307765679 2121772455602703461648519)
              ·
                refine ⟨3182658683404055192472779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121772455602703461648519 3182658683404055192472779)
                ·
                  refine ⟨4773988025106082788709169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182658683404055192472779 4773988025106082788709169)
                  ·
                    refine ⟨3580491018829562091531877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4773988025106082788709169 3580491018829562091531877)
                    ·
                      refine ⟨671342066030542892162227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3580491018829562091531877 671342066030542892162227)
                      ·
                        rfl

theorem cell23_1307434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1307434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307434 prefixEnd_1307434 := by exact prefixLift 1307434
  have htrace : WordTrace (prefixWord ++ tailWord_1307434) baseStart_1307434 baseEnd_1307434 := by
    simpa [prefixWord, tailWord_1307434, baseEnd_1307434] using wordTrace_append hprefix tailTrace_1307434
  have hstable : (prefixWord ++ tailWord_1307434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307434).length < 2 ^ (prefixWord ++ tailWord_1307434).sum := by decide
  have hdescent : baseEnd_1307434 < baseStart_1307434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307436 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_1307436 : Nat := 118140960795 + 1307436 * 2 ^ 59
def prefixEnd_1307436 : Nat := 4983230072969 + 3 ^ 40 * 1307436 * 2
def baseEnd_1307436 : Nat := 223781030997283961445739

theorem tailTrace_1307436 : CollatzResearch.WordTrace tailWord_1307436 prefixEnd_1307436 223781030997283961445739 := by
  unfold tailWord_1307436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23843054245695069568351081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31790738994260092757801441 23843054245695069568351081)
  ·
    refine ⟨17882290684271302176263311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23843054245695069568351081 17882290684271302176263311)
    ·
      refine ⟨26823436026406953264394967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17882290684271302176263311 26823436026406953264394967)
      ·
        refine ⟨40235154039610429896592451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26823436026406953264394967 40235154039610429896592451)
        ·
          refine ⟨60352731059415644844888677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40235154039610429896592451 60352731059415644844888677)
          ·
            refine ⟨11316137073640433408416627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60352731059415644844888677 11316137073640433408416627)
            ·
              refine ⟨16974205610460650112624941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11316137073640433408416627 16974205610460650112624941)
              ·
                refine ⟨6365327103922743792234353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16974205610460650112624941 6365327103922743792234353)
                ·
                  refine ⟨4773995327942057844175765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6365327103922743792234353 4773995327942057844175765)
                  ·
                    refine ⟨223781030997283961445739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4773995327942057844175765 223781030997283961445739)
                    ·
                      rfl

theorem cell23_1307436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_1307436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307436 prefixEnd_1307436 := by exact prefixLift 1307436
  have htrace : WordTrace (prefixWord ++ tailWord_1307436) baseStart_1307436 baseEnd_1307436 := by
    simpa [prefixWord, tailWord_1307436, baseEnd_1307436] using wordTrace_append hprefix tailTrace_1307436
  have hstable : (prefixWord ++ tailWord_1307436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307436).length < 2 ^ (prefixWord ++ tailWord_1307436).sum := by decide
  have hdescent : baseEnd_1307436 < baseStart_1307436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307456 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_1307456 : Nat := 118140960795 + 1307456 * 2 ^ 59
def prefixEnd_1307456 : Nat := 4983230072969 + 3 ^ 40 * 1307456 * 2
def baseEnd_1307456 : Nat := 671353362604941806087125

theorem tailTrace_1307456 : CollatzResearch.WordTrace tailWord_1307456 prefixEnd_1307456 671353362604941806087125 := by
  unfold tailWord_1307456
  simp only [CollatzResearch.WordTrace]
  refine ⟨23843418975658841276215111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31791225300878455034953481 23843418975658841276215111)
  ·
    refine ⟨35765128463488261914322667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23843418975658841276215111 35765128463488261914322667)
    ·
      refine ⟨53647692695232392871484001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35765128463488261914322667 53647692695232392871484001)
      ·
        refine ⟨40235769521424294653613001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53647692695232392871484001 40235769521424294653613001)
        ·
          refine ⟨30176827141068220990209751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40235769521424294653613001 30176827141068220990209751)
          ·
            refine ⟨45265240711602331485314627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30176827141068220990209751 45265240711602331485314627)
            ·
              refine ⟨67897861067403497227971941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45265240711602331485314627 67897861067403497227971941)
              ·
                refine ⟨12730848950138155730244739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67897861067403497227971941 12730848950138155730244739)
                ·
                  refine ⟨19096273425207233595367109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12730848950138155730244739 19096273425207233595367109)
                  ·
                    refine ⟨3580551267226356299131333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19096273425207233595367109 3580551267226356299131333)
                    ·
                      refine ⟨671353362604941806087125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3580551267226356299131333 671353362604941806087125)
                      ·
                        rfl

theorem cell23_1307456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_1307456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307456 prefixEnd_1307456 := by exact prefixLift 1307456
  have htrace : WordTrace (prefixWord ++ tailWord_1307456) baseStart_1307456 baseEnd_1307456 := by
    simpa [prefixWord, tailWord_1307456, baseEnd_1307456] using wordTrace_append hprefix tailTrace_1307456
  have hstable : (prefixWord ++ tailWord_1307456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307456).length < 2 ^ (prefixWord ++ tailWord_1307456).sum := by decide
  have hdescent : baseEnd_1307456 < baseStart_1307456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307477 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1307477 : Nat := 118140960795 + 1307477 * 2 ^ 59
def prefixEnd_1307477 : Nat := 4983230072969 + 3 ^ 40 * 1307477 * 2
def baseEnd_1307477 : Nat := 671364145698686223924529

theorem tailTrace_1307477 : CollatzResearch.WordTrace tailWord_1307477 prefixEnd_1307477 671364145698686223924529 := by
  unfold tailWord_1307477
  simp only [CollatzResearch.WordTrace]
  refine ⟨47687603884241603138944685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31791735922827735425963123 47687603884241603138944685)
  ·
    refine ⟨17882851456590601177104257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47687603884241603138944685 17882851456590601177104257)
    ·
      refine ⟨13412138592442950882828193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17882851456590601177104257 13412138592442950882828193)
      ·
        refine ⟨10059103944332213162121145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13412138592442950882828193 10059103944332213162121145)
        ·
          refine ⟨7544327958249159871590859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10059103944332213162121145 7544327958249159871590859)
          ·
            refine ⟨11316491937373739807386289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7544327958249159871590859 11316491937373739807386289)
            ·
              refine ⟨8487368953030304855539717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11316491937373739807386289 8487368953030304855539717)
              ·
                refine ⟨1591381678693182160413697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8487368953030304855539717 1591381678693182160413697)
                ·
                  refine ⟨1193536259019886620310273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591381678693182160413697 1193536259019886620310273)
                  ·
                    refine ⟨895152194264914965232705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1193536259019886620310273 895152194264914965232705)
                    ·
                      refine ⟨671364145698686223924529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 895152194264914965232705 671364145698686223924529)
                      ·
                        rfl

theorem cell23_1307477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1307477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307477 prefixEnd_1307477 := by exact prefixLift 1307477
  have htrace : WordTrace (prefixWord ++ tailWord_1307477) baseStart_1307477 baseEnd_1307477 := by
    simpa [prefixWord, tailWord_1307477, baseEnd_1307477] using wordTrace_append hprefix tailTrace_1307477
  have hstable : (prefixWord ++ tailWord_1307477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307477).length < 2 ^ (prefixWord ++ tailWord_1307477).sum := by decide
  have hdescent : baseEnd_1307477 < baseStart_1307477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307493 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1307493 : Nat := 118140960795 + 1307493 * 2 ^ 59
def prefixEnd_1307493 : Nat := 4983230072969 + 3 ^ 40 * 1307493 * 2
def baseEnd_1307493 : Nat := 671372361389158161324455

theorem tailTrace_1307493 : CollatzResearch.WordTrace tailWord_1307493 prefixEnd_1307493 671372361389158161324455 := by
  unfold tailWord_1307493
  simp only [CollatzResearch.WordTrace]
  refine ⟨47688187452183637871527133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31792124968122425247684755 47688187452183637871527133)
  ·
    refine ⟨17883070294568864201822675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47688187452183637871527133 17883070294568864201822675)
    ·
      refine ⟨26824605441853296302734013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17883070294568864201822675 26824605441853296302734013)
      ·
        refine ⟨10059227040694986113525255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26824605441853296302734013 10059227040694986113525255)
        ·
          refine ⟨15088840561042479170287883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10059227040694986113525255 15088840561042479170287883)
          ·
            refine ⟨22633260841563718755431825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15088840561042479170287883 22633260841563718755431825)
            ·
              refine ⟨16974945631172789066573869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22633260841563718755431825 16974945631172789066573869)
              ·
                refine ⟨6365604611689795899965201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16974945631172789066573869 6365604611689795899965201)
                ·
                  refine ⟨4774203458767346924973901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6365604611689795899965201 4774203458767346924973901)
                  ·
                    refine ⟨1790326297037755096865213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4774203458767346924973901 1790326297037755096865213)
                    ·
                      refine ⟨671372361389158161324455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1790326297037755096865213 671372361389158161324455)
                      ·
                        rfl

theorem cell23_1307493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1307493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307493 prefixEnd_1307493 := by exact prefixLift 1307493
  have htrace : WordTrace (prefixWord ++ tailWord_1307493) baseStart_1307493 baseEnd_1307493 := by
    simpa [prefixWord, tailWord_1307493, baseEnd_1307493] using wordTrace_append hprefix tailTrace_1307493
  have hstable : (prefixWord ++ tailWord_1307493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307493).length < 2 ^ (prefixWord ++ tailWord_1307493).sum := by decide
  have hdescent : baseEnd_1307493 < baseStart_1307493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307513 : List Nat := [1, 2, 1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_1307513 : Nat := 118140960795 + 1307513 * 2 ^ 59
def prefixEnd_1307513 : Nat := 4983230072969 + 3 ^ 40 * 1307513 * 2
def baseEnd_1307513 : Nat := 223794210334082694358121

theorem tailTrace_1307513 : CollatzResearch.WordTrace tailWord_1307513 prefixEnd_1307513 223794210334082694358121 := by
  unfold tailWord_1307513
  simp only [CollatzResearch.WordTrace]
  refine ⟨47688916912111181287255193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31792611274740787524836795 47688916912111181287255193)
  ·
    refine ⟨35766687684083385965441395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47688916912111181287255193 35766687684083385965441395)
    ·
      refine ⟨53650031526125078948162093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35766687684083385965441395 53650031526125078948162093)
      ·
        refine ⟨20118761822296904605560785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53650031526125078948162093 20118761822296904605560785)
        ·
          refine ⟨15089071366722678454170589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20118761822296904605560785 15089071366722678454170589)
          ·
            refine ⟨5658401762521004420313971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15089071366722678454170589 5658401762521004420313971)
            ·
              refine ⟨8487602643781506630470957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658401762521004420313971 8487602643781506630470957)
              ·
                refine ⟨3182850991418064986426609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8487602643781506630470957 3182850991418064986426609)
                ·
                  refine ⟨2387138243563548739819957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3182850991418064986426609 2387138243563548739819957)
                  ·
                    refine ⟨223794210334082694358121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2387138243563548739819957 223794210334082694358121)
                    ·
                      rfl

theorem cell23_1307513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_1307513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307513 prefixEnd_1307513 := by exact prefixLift 1307513
  have htrace : WordTrace (prefixWord ++ tailWord_1307513) baseStart_1307513 baseEnd_1307513 := by
    simpa [prefixWord, tailWord_1307513, baseEnd_1307513] using wordTrace_append hprefix tailTrace_1307513
  have hstable : (prefixWord ++ tailWord_1307513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307513).length < 2 ^ (prefixWord ++ tailWord_1307513).sum := by decide
  have hdescent : baseEnd_1307513 < baseStart_1307513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307530 : List Nat := [3, 1, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_1307530 : Nat := 118140960795 + 1307530 * 2 ^ 59
def prefixEnd_1307530 : Nat := 4983230072969 + 3 ^ 40 * 1307530 * 2
def baseEnd_1307530 : Nat := 223797120057791505520595

theorem tailTrace_1307530 : CollatzResearch.WordTrace tailWord_1307530 prefixEnd_1307530 223797120057791505520595 := by
  unfold tailWord_1307530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922384238262398297656011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31793024635366395460416029 11922384238262398297656011)
  ·
    refine ⟨17883576357393597446484017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11922384238262398297656011 17883576357393597446484017)
    ·
      refine ⟨13412682268045198084863013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17883576357393597446484017 13412682268045198084863013)
      ·
        refine ⟨2514877925258474640911815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13412682268045198084863013 2514877925258474640911815)
        ·
          refine ⟨3772316887887711961367723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514877925258474640911815 3772316887887711961367723)
          ·
            refine ⟨5658475331831567942051585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772316887887711961367723 5658475331831567942051585)
            ·
              refine ⟨4243856498873675956538689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658475331831567942051585 4243856498873675956538689)
              ·
                refine ⟨3182892374155256967404017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4243856498873675956538689 3182892374155256967404017)
                ·
                  refine ⟨2387169280616442725553013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3182892374155256967404017 2387169280616442725553013)
                  ·
                    refine ⟨223797120057791505520595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2387169280616442725553013 223797120057791505520595)
                    ·
                      rfl

theorem cell23_1307530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_1307530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1307530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1307530 prefixEnd_1307530 := by exact prefixLift 1307530
  have htrace : WordTrace (prefixWord ++ tailWord_1307530) baseStart_1307530 baseEnd_1307530 := by
    simpa [prefixWord, tailWord_1307530, baseEnd_1307530] using wordTrace_append hprefix tailTrace_1307530
  have hstable : (prefixWord ++ tailWord_1307530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307530).length < 2 ^ (prefixWord ++ tailWord_1307530).sum := by decide
  have hdescent : baseEnd_1307530 < baseStart_1307530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
