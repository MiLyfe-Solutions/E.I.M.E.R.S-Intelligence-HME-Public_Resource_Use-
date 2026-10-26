import V185TrunkScan23Chunk0734

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4346312 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 2, 5]
def baseStart_4346312 : Nat := 118140960795 + 4346312 * 2 ^ 59
def prefixEnd_4346312 : Nat := 4983230072969 + 3 ^ 40 * 4346312 * 2
def baseEnd_4346312 : Nat := 743915710134768089337227

theorem tailTrace_4346312 : CollatzResearch.WordTrace tailWord_4346312 prefixEnd_4346312 743915710134768089337227 := by
  unfold tailWord_4346312
  simp only [CollatzResearch.WordTrace]
  refine ⟨79261510915030694918952595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105682014553374259891936793 79261510915030694918952595)
  ·
    refine ⟨118892266372546042378428893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79261510915030694918952595 118892266372546042378428893)
    ·
      refine ⟨44584599889704765891910835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118892266372546042378428893 44584599889704765891910835)
      ·
        refine ⟨66876899834557148837866253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44584599889704765891910835 66876899834557148837866253)
        ·
          refine ⟨25078837437958930814199845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66876899834557148837866253 25078837437958930814199845)
          ·
            refine ⟨4702282019617299527662471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25078837437958930814199845 4702282019617299527662471)
            ·
              refine ⟨7053423029425949291493707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702282019617299527662471 7053423029425949291493707)
              ·
                refine ⟨10580134544138923937240561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053423029425949291493707 10580134544138923937240561)
                ·
                  refine ⟨7935100908104192952930421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10580134544138923937240561 7935100908104192952930421)
                  ·
                    refine ⟨743915710134768089337227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7935100908104192952930421 743915710134768089337227)
                    ·
                      rfl

theorem cell23_4346312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_4346312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346312 prefixEnd_4346312 := by exact prefixLift 4346312
  have htrace : WordTrace (prefixWord ++ tailWord_4346312) baseStart_4346312 baseEnd_4346312 := by
    simpa [prefixWord, tailWord_4346312, baseEnd_4346312] using wordTrace_append hprefix tailTrace_4346312
  have hstable : (prefixWord ++ tailWord_4346312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346312).length < 2 ^ (prefixWord ++ tailWord_4346312).sum := by decide
  have hdescent : baseEnd_4346312 < baseStart_4346312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346315 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 6, 2]
def baseStart_4346315 : Nat := 118140960795 + 4346315 * 2 ^ 59
def prefixEnd_4346315 : Nat := 4983230072969 + 3 ^ 40 * 4346315 * 2
def baseEnd_4346315 : Nat := 2231748670846267756274167

theorem tailTrace_4346315 : CollatzResearch.WordTrace tailWord_4346315 prefixEnd_4346315 2231748670846267756274167 := by
  unfold tailWord_4346315
  simp only [CollatzResearch.WordTrace]
  refine ⟨158523131249050521350264399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105682087499367014233509599 158523131249050521350264399)
  ·
    refine ⟨237784696873575782025396599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158523131249050521350264399 237784696873575782025396599)
    ·
      refine ⟨356677045310363673038094899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237784696873575782025396599 356677045310363673038094899)
      ·
        refine ⟨535015567965545509557142349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356677045310363673038094899 535015567965545509557142349)
        ·
          refine ⟨200630837987079566083928381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535015567965545509557142349 200630837987079566083928381)
          ·
            refine ⟨75236564245154837281473143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200630837987079566083928381 75236564245154837281473143)
            ·
              refine ⟨112854846367732255922209715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75236564245154837281473143 112854846367732255922209715)
              ·
                refine ⟨169282269551598383883314573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112854846367732255922209715 169282269551598383883314573)
                ·
                  refine ⟨63480851081849393956242965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169282269551598383883314573 63480851081849393956242965)
                  ·
                    refine ⟨2975664894461690341698889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63480851081849393956242965 2975664894461690341698889)
                    ·
                      refine ⟨2231748670846267756274167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975664894461690341698889 2231748670846267756274167)
                      ·
                        rfl

theorem cell23_4346315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6, 2].length) (baseStart_4346315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346315 prefixEnd_4346315 := by exact prefixLift 4346315
  have htrace : WordTrace (prefixWord ++ tailWord_4346315) baseStart_4346315 baseEnd_4346315 := by
    simpa [prefixWord, tailWord_4346315, baseEnd_4346315] using wordTrace_append hprefix tailTrace_4346315
  have hstable : (prefixWord ++ tailWord_4346315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346315).length < 2 ^ (prefixWord ++ tailWord_4346315).sum := by decide
  have hdescent : baseEnd_4346315 < baseStart_4346315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346349 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4346349 : Nat := 118140960795 + 4346349 * 2 ^ 59
def prefixEnd_4346349 : Nat := 4983230072969 + 3 ^ 40 * 4346349 * 2
def baseEnd_4346349 : Nat := 2231766129188520623249011

theorem tailTrace_4346349 : CollatzResearch.WordTrace tailWord_4346349 prefixEnd_4346349 2231766129188520623249011 := by
  unfold tailWord_4346349
  simp only [CollatzResearch.WordTrace]
  refine ⟨158524371330927345157002101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105682914220618230104668067 158524371330927345157002101)
  ·
    refine ⟨14861659812274438608468947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158524371330927345157002101 14861659812274438608468947)
    ·
      refine ⟨22292489718411657912703421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14861659812274438608468947 22292489718411657912703421)
      ·
        refine ⟨8359683644404371717263783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22292489718411657912703421 8359683644404371717263783)
        ·
          refine ⟨12539525466606557575895675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8359683644404371717263783 12539525466606557575895675)
          ·
            refine ⟨18809288199909836363843513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12539525466606557575895675 18809288199909836363843513)
            ·
              refine ⟨14106966149932377272882635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18809288199909836363843513 14106966149932377272882635)
              ·
                refine ⟨21160449224898565909323953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14106966149932377272882635 21160449224898565909323953)
                ·
                  refine ⟨15870336918673924431992965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21160449224898565909323953 15870336918673924431992965)
                  ·
                    refine ⟨2975688172251360830998681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15870336918673924431992965 2975688172251360830998681)
                    ·
                      refine ⟨2231766129188520623249011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975688172251360830998681 2231766129188520623249011)
                      ·
                        rfl

theorem cell23_4346349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4346349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346349 prefixEnd_4346349 := by exact prefixLift 4346349
  have htrace : WordTrace (prefixWord ++ tailWord_4346349) baseStart_4346349 baseEnd_4346349 := by
    simpa [prefixWord, tailWord_4346349, baseEnd_4346349] using wordTrace_append hprefix tailTrace_4346349
  have hstable : (prefixWord ++ tailWord_4346349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346349).length < 2 ^ (prefixWord ++ tailWord_4346349).sum := by decide
  have hdescent : baseEnd_4346349 < baseStart_4346349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346365 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_4346365 : Nat := 118140960795 + 4346365 * 2 ^ 59
def prefixEnd_4346365 : Nat := 4983230072969 + 3 ^ 40 * 4346365 * 2
def baseEnd_4346365 : Nat := 2231774344878992560648937

theorem tailTrace_4346365 : CollatzResearch.WordTrace tailWord_4346365 prefixEnd_4346365 2231774344878992560648937 := by
  unfold tailWord_4346365
  simp only [CollatzResearch.WordTrace]
  refine ⟨158524954898869379889584549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105683303265912919926389699 158524954898869379889584549)
  ·
    refine ⟨29723429043538008729297103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158524954898869379889584549 29723429043538008729297103)
    ·
      refine ⟨44585143565307013093945655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29723429043538008729297103 44585143565307013093945655)
      ·
        refine ⟨66877715347960519640918483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44585143565307013093945655 66877715347960519640918483)
        ·
          refine ⟨100316573021940779461377725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66877715347960519640918483 100316573021940779461377725)
          ·
            refine ⟨37618714883227792298016647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100316573021940779461377725 37618714883227792298016647)
            ·
              refine ⟨56428072324841688447024971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37618714883227792298016647 56428072324841688447024971)
              ·
                refine ⟨84642108487262532670537457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56428072324841688447024971 84642108487262532670537457)
                ·
                  refine ⟨63481581365446899502903093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84642108487262532670537457 63481581365446899502903093)
                  ·
                    refine ⟨5951398253010646828397165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63481581365446899502903093 5951398253010646828397165)
                    ·
                      refine ⟨2231774344878992560648937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5951398253010646828397165 2231774344878992560648937)
                      ·
                        rfl

theorem cell23_4346365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_4346365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346365 prefixEnd_4346365 := by exact prefixLift 4346365
  have htrace : WordTrace (prefixWord ++ tailWord_4346365) baseStart_4346365 baseEnd_4346365 := by
    simpa [prefixWord, tailWord_4346365, baseEnd_4346365] using wordTrace_append hprefix tailTrace_4346365
  have hstable : (prefixWord ++ tailWord_4346365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346365).length < 2 ^ (prefixWord ++ tailWord_4346365).sum := by decide
  have hdescent : baseEnd_4346365 < baseStart_4346365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346368 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_4346368 : Nat := 118140960795 + 4346368 * 2 ^ 59
def prefixEnd_4346368 : Nat := 4983230072969 + 3 ^ 40 * 4346368 * 2
def baseEnd_4346368 : Nat := 743925295106985349637141

theorem tailTrace_4346368 : CollatzResearch.WordTrace tailWord_4346368 prefixEnd_4346368 743925295106985349637141 := by
  unfold tailWord_4346368
  simp only [CollatzResearch.WordTrace]
  refine ⟨79262532158929255700971879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105683376211905674267962505 79262532158929255700971879)
  ·
    refine ⟨118893798238393883551457819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79262532158929255700971879 118893798238393883551457819)
    ·
      refine ⟨178340697357590825327186729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118893798238393883551457819 178340697357590825327186729)
      ·
        refine ⟨133755523018193118995390047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178340697357590825327186729 133755523018193118995390047)
        ·
          refine ⟨200633284527289678493085071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133755523018193118995390047 200633284527289678493085071)
          ·
            refine ⟨300949926790934517739627607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200633284527289678493085071 300949926790934517739627607)
            ·
              refine ⟨451424890186401776609441411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300949926790934517739627607 451424890186401776609441411)
              ·
                refine ⟨677137335279602664914162117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451424890186401776609441411 677137335279602664914162117)
                ·
                  refine ⟨126963250364925499671405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 677137335279602664914162117 126963250364925499671405397)
                  ·
                    refine ⟨743925295106985349637141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126963250364925499671405397 743925295106985349637141)
                    ·
                      rfl

theorem cell23_4346368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_4346368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346368 prefixEnd_4346368 := by exact prefixLift 4346368
  have htrace : WordTrace (prefixWord ++ tailWord_4346368) baseStart_4346368 baseEnd_4346368 := by
    simpa [prefixWord, tailWord_4346368, baseEnd_4346368] using wordTrace_append hprefix tailTrace_4346368
  have hstable : (prefixWord ++ tailWord_4346368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346368).length < 2 ^ (prefixWord ++ tailWord_4346368).sum := by decide
  have hdescent : baseEnd_4346368 < baseStart_4346368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346442 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_4346442 : Nat := 118140960795 + 4346442 * 2 ^ 59
def prefixEnd_4346442 : Nat := 4983230072969 + 3 ^ 40 * 4346442 * 2
def baseEnd_4346442 : Nat := 2231813882889388759386083

theorem tailTrace_4346442 : CollatzResearch.WordTrace tailWord_4346442 prefixEnd_4346442 2231813882889388759386083 := by
  unfold tailWord_4346442
  simp only [CollatzResearch.WordTrace]
  refine ⟨39631940829897605510034395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105685175546393614693425053 39631940829897605510034395)
  ·
    refine ⟨59447911244846408265051593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39631940829897605510034395 59447911244846408265051593)
    ·
      refine ⟨44585933433634806198788695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59447911244846408265051593 44585933433634806198788695)
      ·
        refine ⟨66878900150452209298183043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44585933433634806198788695 66878900150452209298183043)
        ·
          refine ⟨100318350225678313947274565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66878900150452209298183043 100318350225678313947274565)
          ·
            refine ⟨18809690667314683865113981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100318350225678313947274565 18809690667314683865113981)
            ·
              refine ⟨7053634000243006449417743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18809690667314683865113981 7053634000243006449417743)
              ·
                refine ⟨10580451000364509674126615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053634000243006449417743 10580451000364509674126615)
                ·
                  refine ⟨15870676500546764511189923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10580451000364509674126615 15870676500546764511189923)
                  ·
                    refine ⟨23806014750820146766784885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15870676500546764511189923 23806014750820146766784885)
                    ·
                      refine ⟨2231813882889388759386083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23806014750820146766784885 2231813882889388759386083)
                      ·
                        rfl

theorem cell23_4346442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_4346442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346442 prefixEnd_4346442 := by exact prefixLift 4346442
  have htrace : WordTrace (prefixWord ++ tailWord_4346442) baseStart_4346442 baseEnd_4346442 := by
    simpa [prefixWord, tailWord_4346442, baseEnd_4346442] using wordTrace_append hprefix tailTrace_4346442
  have hstable : (prefixWord ++ tailWord_4346442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346442).length < 2 ^ (prefixWord ++ tailWord_4346442).sum := by decide
  have hdescent : baseEnd_4346442 < baseStart_4346442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346449 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 2, 4]
def baseStart_4346449 : Nat := 118140960795 + 4346449 * 2 ^ 59
def prefixEnd_4346449 : Nat := 4983230072969 + 3 ^ 40 * 4346449 * 2
def baseEnd_4346449 : Nat := 743939159084656743999517

theorem tailTrace_4346449 : CollatzResearch.WordTrace tailWord_4346449 prefixEnd_4346449 743939159084656743999517 := by
  unfold tailWord_4346449
  simp only [CollatzResearch.WordTrace]
  refine ⟨158528018630565062235642401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105685345753710041490428267 158528018630565062235642401)
  ·
    refine ⟨118896013972923796676731801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158528018630565062235642401 118896013972923796676731801)
    ·
      refine ⟨89172010479692847507548851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118896013972923796676731801 89172010479692847507548851)
      ·
        refine ⟨133758015719539271261323277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89172010479692847507548851 133758015719539271261323277)
        ·
          refine ⟨50159255894827226722996229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133758015719539271261323277 50159255894827226722996229)
          ·
            refine ⟨9404860480280105010561793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50159255894827226722996229 9404860480280105010561793)
            ·
              refine ⟨7053645360210078757921345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9404860480280105010561793 7053645360210078757921345)
              ·
                refine ⟨5290234020157559068441009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7053645360210078757921345 5290234020157559068441009)
                ·
                  refine ⟨3967675515118169301330757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5290234020157559068441009 3967675515118169301330757)
                  ·
                    refine ⟨743939159084656743999517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3967675515118169301330757 743939159084656743999517)
                    ·
                      rfl

theorem cell23_4346449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_4346449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346449 prefixEnd_4346449 := by exact prefixLift 4346449
  have htrace : WordTrace (prefixWord ++ tailWord_4346449) baseStart_4346449 baseEnd_4346449 := by
    simpa [prefixWord, tailWord_4346449, baseEnd_4346449] using wordTrace_append hprefix tailTrace_4346449
  have hstable : (prefixWord ++ tailWord_4346449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346449).length < 2 ^ (prefixWord ++ tailWord_4346449).sum := by decide
  have hdescent : baseEnd_4346449 < baseStart_4346449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346466 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4346466 : Nat := 118140960795 + 4346466 * 2 ^ 59
def prefixEnd_4346466 : Nat := 4983230072969 + 3 ^ 40 * 4346466 * 2
def baseEnd_4346466 : Nat := 743942068808365555161991

theorem tailTrace_4346466 : CollatzResearch.WordTrace tailWord_4346466 prefixEnd_4346466 743942068808365555161991 := by
  unfold tailWord_4346466
  simp only [CollatzResearch.WordTrace]
  refine ⟨39632159667875868534752813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105685759114335649426007501 39632159667875868534752813)
  ·
    refine ⟨14862059875453450700532305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39632159667875868534752813 14862059875453450700532305)
    ·
      refine ⟨11146544906590088025399229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14862059875453450700532305 11146544906590088025399229)
      ·
        refine ⟨4179954339971283009524711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11146544906590088025399229 4179954339971283009524711)
        ·
          refine ⟨6269931509956924514287067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179954339971283009524711 6269931509956924514287067)
          ·
            refine ⟨9404897264935386771430601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269931509956924514287067 9404897264935386771430601)
            ·
              refine ⟨7053672948701540078572951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9404897264935386771430601 7053672948701540078572951)
              ·
                refine ⟨10580509423052310117859427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053672948701540078572951 10580509423052310117859427)
                ·
                  refine ⟨15870764134578465176789141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10580509423052310117859427 15870764134578465176789141)
                  ·
                    refine ⟨743942068808365555161991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15870764134578465176789141 743942068808365555161991)
                    ·
                      rfl

theorem cell23_4346466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4346466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346466 prefixEnd_4346466 := by exact prefixLift 4346466
  have htrace : WordTrace (prefixWord ++ tailWord_4346466) baseStart_4346466 baseEnd_4346466 := by
    simpa [prefixWord, tailWord_4346466, baseEnd_4346466] using wordTrace_append hprefix tailTrace_4346466
  have hstable : (prefixWord ++ tailWord_4346466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346466).length < 2 ^ (prefixWord ++ tailWord_4346466).sum := by decide
  have hdescent : baseEnd_4346466 < baseStart_4346466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346469 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_4346469 : Nat := 118140960795 + 4346469 * 2 ^ 59
def prefixEnd_4346469 : Nat := 4983230072969 + 3 ^ 40 * 4346469 * 2
def baseEnd_4346469 : Nat := 2231827746867060153748459

theorem tailTrace_4346469 : CollatzResearch.WordTrace tailWord_4346469 prefixEnd_4346469 2231827746867060153748459 := by
  unfold tailWord_4346469
  simp only [CollatzResearch.WordTrace]
  refine ⟨158528748090492605651370461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105685832060328403767580307 158528748090492605651370461)
  ·
    refine ⟨59448280533934727119263923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158528748090492605651370461 59448280533934727119263923)
    ·
      refine ⟨89172420800902090678895885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59448280533934727119263923 89172420800902090678895885)
      ·
        refine ⟨33439657800338284004585957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89172420800902090678895885 33439657800338284004585957)
        ·
          refine ⟨6269935837563428250859867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33439657800338284004585957 6269935837563428250859867)
          ·
            refine ⟨9404903756345142376289801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269935837563428250859867 9404903756345142376289801)
            ·
              refine ⟨7053677817258856782217351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9404903756345142376289801 7053677817258856782217351)
              ·
                refine ⟨10580516725888285173326027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053677817258856782217351 10580516725888285173326027)
                ·
                  refine ⟨15870775088832427759989041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10580516725888285173326027 15870775088832427759989041)
                  ·
                    refine ⟨11903081316624320819991781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15870775088832427759989041 11903081316624320819991781)
                    ·
                      refine ⟨2231827746867060153748459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11903081316624320819991781 2231827746867060153748459)
                      ·
                        rfl

theorem cell23_4346469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_4346469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346469 prefixEnd_4346469 := by exact prefixLift 4346469
  have htrace : WordTrace (prefixWord ++ tailWord_4346469) baseStart_4346469 baseEnd_4346469 := by
    simpa [prefixWord, tailWord_4346469, baseEnd_4346469] using wordTrace_append hprefix tailTrace_4346469
  have hstable : (prefixWord ++ tailWord_4346469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346469).length < 2 ^ (prefixWord ++ tailWord_4346469).sum := by decide
  have hdescent : baseEnd_4346469 < baseStart_4346469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346493 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_4346493 : Nat := 118140960795 + 4346493 * 2 ^ 59
def prefixEnd_4346493 : Nat := 4983230072969 + 3 ^ 40 * 4346493 * 2
def baseEnd_4346493 : Nat := 2231840070402768059848349

theorem tailTrace_4346493 : CollatzResearch.WordTrace tailWord_4346493 prefixEnd_4346493 2231840070402768059848349 := by
  unfold tailWord_4346493
  simp only [CollatzResearch.WordTrace]
  refine ⟨158529623442405657750244133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105686415628270438500162755 158529623442405657750244133)
  ·
    refine ⟨29724304395451060828170775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158529623442405657750244133 29724304395451060828170775)
    ·
      refine ⟨44586456593176591242256163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29724304395451060828170775 44586456593176591242256163)
      ·
        refine ⟨66879684889764886863384245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44586456593176591242256163 66879684889764886863384245)
        ·
          refine ⟨6269970458415458143442273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66879684889764886863384245 6269970458415458143442273)
          ·
            refine ⟨4702477843811593607581705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269970458415458143442273 4702477843811593607581705)
            ·
              refine ⟨3526858382858695205686279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702477843811593607581705 3526858382858695205686279)
              ·
                refine ⟨5290287574288042808529419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526858382858695205686279 5290287574288042808529419)
                ·
                  refine ⟨7935431361432064212794129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5290287574288042808529419 7935431361432064212794129)
                  ·
                    refine ⟨5951573521074048159595597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7935431361432064212794129 5951573521074048159595597)
                    ·
                      refine ⟨2231840070402768059848349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5951573521074048159595597 2231840070402768059848349)
                      ·
                        rfl

theorem cell23_4346493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_4346493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346493 prefixEnd_4346493 := by exact prefixLift 4346493
  have htrace : WordTrace (prefixWord ++ tailWord_4346493) baseStart_4346493 baseEnd_4346493 := by
    simpa [prefixWord, tailWord_4346493, baseEnd_4346493] using wordTrace_append hprefix tailTrace_4346493
  have hstable : (prefixWord ++ tailWord_4346493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346493).length < 2 ^ (prefixWord ++ tailWord_4346493).sum := by decide
  have hdescent : baseEnd_4346493 < baseStart_4346493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346495 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_4346495 : Nat := 118140960795 + 4346495 * 2 ^ 59
def prefixEnd_4346495 : Nat := 4983230072969 + 3 ^ 40 * 4346495 * 2
def baseEnd_4346495 : Nat := 2231841097364077052023339

theorem tailTrace_4346495 : CollatzResearch.WordTrace tailWord_4346495 prefixEnd_4346495 2231841097364077052023339 := by
  unfold tailWord_4346495
  simp only [CollatzResearch.WordTrace]
  refine ⟨158529696388398412091816939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105686464258932274727877959 158529696388398412091816939)
  ·
    refine ⟨237794544582597618137725409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158529696388398412091816939 237794544582597618137725409)
    ·
      refine ⟨178345908436948213603294057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237794544582597618137725409 178345908436948213603294057)
      ·
        refine ⟨133759431327711160202470543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178345908436948213603294057 133759431327711160202470543)
        ·
          refine ⟨200639146991566740303705815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133759431327711160202470543 200639146991566740303705815)
          ·
            refine ⟨300958720487350110455558723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200639146991566740303705815 300958720487350110455558723)
            ·
              refine ⟨451438080731025165683338085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300958720487350110455558723 451438080731025165683338085)
              ·
                refine ⟨84644640137067218565625891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451438080731025165683338085 84644640137067218565625891)
                ·
                  refine ⟨126966960205600827848438837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84644640137067218565625891 126966960205600827848438837)
                  ·
                    refine ⟨11903152519275077610791141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126966960205600827848438837 11903152519275077610791141)
                    ·
                      refine ⟨2231841097364077052023339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11903152519275077610791141 2231841097364077052023339)
                      ·
                        rfl

theorem cell23_4346495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_4346495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346495 prefixEnd_4346495 := by exact prefixLift 4346495
  have htrace : WordTrace (prefixWord ++ tailWord_4346495) baseStart_4346495 baseEnd_4346495 := by
    simpa [prefixWord, tailWord_4346495, baseEnd_4346495] using wordTrace_append hprefix tailTrace_4346495
  have hstable : (prefixWord ++ tailWord_4346495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346495).length < 2 ^ (prefixWord ++ tailWord_4346495).sum := by decide
  have hdescent : baseEnd_4346495 < baseStart_4346495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346506 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_4346506 : Nat := 118140960795 + 4346506 * 2 ^ 59
def prefixEnd_4346506 : Nat := 4983230072969 + 3 ^ 40 * 4346506 * 2
def baseEnd_4346506 : Nat := 2231846745651276508985789

theorem tailTrace_4346506 : CollatzResearch.WordTrace tailWord_4346506 prefixEnd_4346506 2231846745651276508985789 := by
  unfold tailWord_4346506
  simp only [CollatzResearch.WordTrace]
  refine ⟨39632524397839640242616843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105686731727572373980311581 39632524397839640242616843)
  ·
    refine ⟨59448786596759460363925265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39632524397839640242616843 59448786596759460363925265)
    ·
      refine ⟨44586589947569595272943949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59448786596759460363925265 44586589947569595272943949)
      ·
        refine ⟨16719971230338598227353981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44586589947569595272943949 16719971230338598227353981)
        ·
          refine ⟨6269989211376974335257743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16719971230338598227353981 6269989211376974335257743)
          ·
            refine ⟨9404983817065461502886615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269989211376974335257743 9404983817065461502886615)
            ·
              refine ⟨14107475725598192254329923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9404983817065461502886615 14107475725598192254329923)
              ·
                refine ⟨21161213588397288381494885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14107475725598192254329923 21161213588397288381494885)
                ·
                  refine ⟨3967727547824491571530291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21161213588397288381494885 3967727547824491571530291)
                  ·
                    refine ⟨5951591321736737357295437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3967727547824491571530291 5951591321736737357295437)
                    ·
                      refine ⟨2231846745651276508985789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5951591321736737357295437 2231846745651276508985789)
                      ·
                        rfl

theorem cell23_4346506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_4346506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346506 prefixEnd_4346506 := by exact prefixLift 4346506
  have htrace : WordTrace (prefixWord ++ tailWord_4346506) baseStart_4346506 baseEnd_4346506 := by
    simpa [prefixWord, tailWord_4346506, baseEnd_4346506] using wordTrace_append hprefix tailTrace_4346506
  have hstable : (prefixWord ++ tailWord_4346506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346506).length < 2 ^ (prefixWord ++ tailWord_4346506).sum := by decide
  have hdescent : baseEnd_4346506 < baseStart_4346506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346512 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 8, 2]
def baseStart_4346512 : Nat := 118140960795 + 4346512 * 2 ^ 59
def prefixEnd_4346512 : Nat := 4983230072969 + 3 ^ 40 * 4346512 * 2
def baseEnd_4346512 : Nat := 2231849826535203485510761

theorem tailTrace_4346512 : CollatzResearch.WordTrace tailWord_4346512 prefixEnd_4346512 2231849826535203485510761 := by
  unfold tailWord_4346512
  simp only [CollatzResearch.WordTrace]
  refine ⟨79265158214668411997592895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105686877619557882663457193 79265158214668411997592895)
  ·
    refine ⟨118897737322002617996389343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79265158214668411997592895 118897737322002617996389343)
    ·
      refine ⟨178346605983003926994584015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118897737322002617996389343 178346605983003926994584015)
      ·
        refine ⟨267519908974505890491876023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178346605983003926994584015 267519908974505890491876023)
        ·
          refine ⟨401279863461758835737814035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267519908974505890491876023 401279863461758835737814035)
          ·
            refine ⟨601919795192638253606721053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401279863461758835737814035 601919795192638253606721053)
            ·
              refine ⟨225719923197239345102520395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601919795192638253606721053 225719923197239345102520395)
              ·
                refine ⟨338579884795859017653780593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225719923197239345102520395 338579884795859017653780593)
                ·
                  refine ⟨253934913596894263240335445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338579884795859017653780593 253934913596894263240335445)
                  ·
                    refine ⟨2975799768713604647347681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 253934913596894263240335445 2975799768713604647347681)
                    ·
                      refine ⟨2231849826535203485510761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975799768713604647347681 2231849826535203485510761)
                      ·
                        rfl

theorem cell23_4346512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 8, 2].length) (baseStart_4346512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346512 prefixEnd_4346512 := by exact prefixLift 4346512
  have htrace : WordTrace (prefixWord ++ tailWord_4346512) baseStart_4346512 baseEnd_4346512 := by
    simpa [prefixWord, tailWord_4346512, baseEnd_4346512] using wordTrace_append hprefix tailTrace_4346512
  have hstable : (prefixWord ++ tailWord_4346512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346512).length < 2 ^ (prefixWord ++ tailWord_4346512).sum := by decide
  have hdescent : baseEnd_4346512 < baseStart_4346512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346515 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_4346515 : Nat := 118140960795 + 4346515 * 2 ^ 59
def prefixEnd_4346515 : Nat := 4983230072969 + 3 ^ 40 * 4346515 * 2
def baseEnd_4346515 : Nat := 2231851366977166973773247

theorem tailTrace_4346515 : CollatzResearch.WordTrace tailWord_4346515 prefixEnd_4346515 2231851366977166973773247 := by
  unfold tailWord_4346515
  simp only [CollatzResearch.WordTrace]
  refine ⟨158530425848325955507544999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105686950565550637005029999 158530425848325955507544999)
  ·
    refine ⟨237795638772488933261317499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158530425848325955507544999 237795638772488933261317499)
    ·
      refine ⟨356693458158733399891976249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237795638772488933261317499 356693458158733399891976249)
      ·
        refine ⟨267520093619050049918982187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356693458158733399891976249 267520093619050049918982187)
        ·
          refine ⟨401280140428575074878473281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267520093619050049918982187 401280140428575074878473281)
          ·
            refine ⟨300960105321431306158854961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401280140428575074878473281 300960105321431306158854961)
            ·
              refine ⟨225720078991073479619141221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300960105321431306158854961 225720078991073479619141221)
              ·
                refine ⟨42322514810826277428588979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225720078991073479619141221 42322514810826277428588979)
                ·
                  refine ⟨63483772216239416142883469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42322514810826277428588979 63483772216239416142883469)
                  ·
                    refine ⟨23806414581089781053581301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63483772216239416142883469 23806414581089781053581301)
                    ·
                      refine ⟨2231851366977166973773247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23806414581089781053581301 2231851366977166973773247)
                      ·
                        rfl

theorem cell23_4346515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_4346515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346515 prefixEnd_4346515 := by exact prefixLift 4346515
  have htrace : WordTrace (prefixWord ++ tailWord_4346515) baseStart_4346515 baseEnd_4346515 := by
    simpa [prefixWord, tailWord_4346515, baseEnd_4346515] using wordTrace_append hprefix tailTrace_4346515
  have hstable : (prefixWord ++ tailWord_4346515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346515).length < 2 ^ (prefixWord ++ tailWord_4346515).sum := by decide
  have hdescent : baseEnd_4346515 < baseStart_4346515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346532 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_4346532 : Nat := 118140960795 + 4346532 * 2 ^ 59
def prefixEnd_4346532 : Nat := 4983230072969 + 3 ^ 40 * 4346532 * 2
def baseEnd_4346532 : Nat := 2231860096148293407260669

theorem tailTrace_4346532 : CollatzResearch.WordTrace tailWord_4346532 prefixEnd_4346532 2231860096148293407260669 := by
  unfold tailWord_4346532
  simp only [CollatzResearch.WordTrace]
  refine ⟨79265522944632183705456925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105687363926176244940609233 79265522944632183705456925)
  ·
    refine ⟨29724571104237068889546347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79265522944632183705456925 29724571104237068889546347)
    ·
      refine ⟨44586856656355603334319521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29724571104237068889546347 44586856656355603334319521)
      ·
        refine ⟨33440142492266702500739641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44586856656355603334319521 33440142492266702500739641)
        ·
          refine ⟨25080106869200026875554731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33440142492266702500739641 25080106869200026875554731)
          ·
            refine ⟨37620160303800040313332097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25080106869200026875554731 37620160303800040313332097)
            ·
              refine ⟨28215120227850030234999073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37620160303800040313332097 28215120227850030234999073)
              ·
                refine ⟨21161340170887522676249305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28215120227850030234999073 21161340170887522676249305)
                ·
                  refine ⟨15871005128165642007186979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21161340170887522676249305 15871005128165642007186979)
                  ·
                    refine ⟨23806507692248463010780469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15871005128165642007186979 23806507692248463010780469)
                    ·
                      refine ⟨2231860096148293407260669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23806507692248463010780469 2231860096148293407260669)
                      ·
                        rfl

theorem cell23_4346532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_4346532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346532 prefixEnd_4346532 := by exact prefixLift 4346532
  have htrace : WordTrace (prefixWord ++ tailWord_4346532) baseStart_4346532 baseEnd_4346532 := by
    simpa [prefixWord, tailWord_4346532, baseEnd_4346532] using wordTrace_append hprefix tailTrace_4346532
  have hstable : (prefixWord ++ tailWord_4346532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346532).length < 2 ^ (prefixWord ++ tailWord_4346532).sum := by decide
  have hdescent : baseEnd_4346532 < baseStart_4346532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346549 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4346549 : Nat := 118140960795 + 4346549 * 2 ^ 59
def prefixEnd_4346549 : Nat := 4983230072969 + 3 ^ 40 * 4346549 * 2
def baseEnd_4346549 : Nat := 2231868825319419840748091

theorem tailTrace_4346549 : CollatzResearch.WordTrace tailWord_4346549 prefixEnd_4346549 2231868825319419840748091 := by
  unfold tailWord_4346549
  simp only [CollatzResearch.WordTrace]
  refine ⟨158531665930202779314282701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105687777286801852876188467 158531665930202779314282701)
  ·
    refine ⟨59449374723826042242856013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158531665930202779314282701 59449374723826042242856013)
    ·
      refine ⟨22293515521434765841071005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59449374723826042242856013 22293515521434765841071005)
      ·
        refine ⟨8360068320538037190401627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22293515521434765841071005 8360068320538037190401627)
        ·
          refine ⟨12540102480807055785602441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8360068320538037190401627 12540102480807055785602441)
          ·
            refine ⟨9405076860605291839201831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12540102480807055785602441 9405076860605291839201831)
            ·
              refine ⟨14107615290907937758802747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9405076860605291839201831 14107615290907937758802747)
              ·
                refine ⟨21161422936361906638204121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14107615290907937758802747 21161422936361906638204121)
                ·
                  refine ⟨15871067202271429978653091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21161422936361906638204121 15871067202271429978653091)
                  ·
                    refine ⟨23806600803407144967979637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15871067202271429978653091 23806600803407144967979637)
                    ·
                      refine ⟨2231868825319419840748091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23806600803407144967979637 2231868825319419840748091)
                      ·
                        rfl

theorem cell23_4346549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4346549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346549 prefixEnd_4346549 := by exact prefixLift 4346549
  have htrace : WordTrace (prefixWord ++ tailWord_4346549) baseStart_4346549 baseEnd_4346549 := by
    simpa [prefixWord, tailWord_4346549, baseEnd_4346549] using wordTrace_append hprefix tailTrace_4346549
  have hstable : (prefixWord ++ tailWord_4346549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346549).length < 2 ^ (prefixWord ++ tailWord_4346549).sum := by decide
  have hdescent : baseEnd_4346549 < baseStart_4346549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346555 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_4346555 : Nat := 118140960795 + 4346555 * 2 ^ 59
def prefixEnd_4346555 : Nat := 4983230072969 + 3 ^ 40 * 4346555 * 2
def baseEnd_4346555 : Nat := 2231871906203346817273063

theorem tailTrace_4346555 : CollatzResearch.WordTrace tailWord_4346555 prefixEnd_4346555 2231871906203346817273063 := by
  unfold tailWord_4346555
  simp only [CollatzResearch.WordTrace]
  refine ⟨158531884768181042339001119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105687923178787361559334079 158531884768181042339001119)
  ·
    refine ⟨237797827152271563508501679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158531884768181042339001119 237797827152271563508501679)
    ·
      refine ⟨356696740728407345262752519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237797827152271563508501679 356696740728407345262752519)
      ·
        refine ⟨535045111092611017894128779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356696740728407345262752519 535045111092611017894128779)
        ·
          refine ⟨802567666638916526841193169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535045111092611017894128779 802567666638916526841193169)
          ·
            refine ⟨601925749979187395130894877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802567666638916526841193169 601925749979187395130894877)
            ·
              refine ⟨225722156242195273174085579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601925749979187395130894877 225722156242195273174085579)
              ·
                refine ⟨338583234363292909761128369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225722156242195273174085579 338583234363292909761128369)
                ·
                  refine ⟨253937425772469682320846277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338583234363292909761128369 253937425772469682320846277)
                  ·
                    refine ⟨47613267332338065435158677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 253937425772469682320846277 47613267332338065435158677)
                    ·
                      refine ⟨2231871906203346817273063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47613267332338065435158677 2231871906203346817273063)
                      ·
                        rfl

theorem cell23_4346555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_4346555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346555 prefixEnd_4346555 := by exact prefixLift 4346555
  have htrace : WordTrace (prefixWord ++ tailWord_4346555) baseStart_4346555 baseEnd_4346555 := by
    simpa [prefixWord, tailWord_4346555, baseEnd_4346555] using wordTrace_append hprefix tailTrace_4346555
  have hstable : (prefixWord ++ tailWord_4346555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346555).length < 2 ^ (prefixWord ++ tailWord_4346555).sum := by decide
  have hdescent : baseEnd_4346555 < baseStart_4346555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346580 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4346580 : Nat := 118140960795 + 4346580 * 2 ^ 59
def prefixEnd_4346580 : Nat := 4983230072969 + 3 ^ 40 * 4346580 * 2
def baseEnd_4346580 : Nat := 2231884743219709219460449

theorem tailTrace_4346580 : CollatzResearch.WordTrace tailWord_4346580 prefixEnd_4346580 2231884743219709219460449 := by
  unfold tailWord_4346580
  simp only [CollatzResearch.WordTrace]
  refine ⟨79266398296545235804330597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105688531062060314405774129 79266398296545235804330597)
  ·
    refine ⟨14862449680602231713311987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79266398296545235804330597 14862449680602231713311987)
    ·
      refine ⟨22293674520903347569967981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14862449680602231713311987 22293674520903347569967981)
      ·
        refine ⟨8360127945338755338737993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22293674520903347569967981 8360127945338755338737993)
        ·
          refine ⟨6270095959004066504053495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8360127945338755338737993 6270095959004066504053495)
          ·
            refine ⟨9405143938506099756080243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6270095959004066504053495 9405143938506099756080243)
            ·
              refine ⟨14107715907759149634120365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9405143938506099756080243 14107715907759149634120365)
              ·
                refine ⟨5290393465409681112795137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14107715907759149634120365 5290393465409681112795137)
                ·
                  refine ⟨3967795099057260834596353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5290393465409681112795137 3967795099057260834596353)
                  ·
                    refine ⟨2975846324292945625947265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3967795099057260834596353 2975846324292945625947265)
                    ·
                      refine ⟨2231884743219709219460449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2975846324292945625947265 2231884743219709219460449)
                      ·
                        rfl

theorem cell23_4346580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4346580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346580 prefixEnd_4346580 := by exact prefixLift 4346580
  have htrace : WordTrace (prefixWord ++ tailWord_4346580) baseStart_4346580 baseEnd_4346580 := by
    simpa [prefixWord, tailWord_4346580, baseEnd_4346580] using wordTrace_append hprefix tailTrace_4346580
  have hstable : (prefixWord ++ tailWord_4346580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346580).length < 2 ^ (prefixWord ++ tailWord_4346580).sum := by decide
  have hdescent : baseEnd_4346580 < baseStart_4346580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346656 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4346656 : Nat := 118140960795 + 4346656 * 2 ^ 59
def prefixEnd_4346656 : Nat := 4983230072969 + 3 ^ 40 * 4346656 * 2
def baseEnd_4346656 : Nat := 2231923767749450922110099

theorem tailTrace_4346656 : CollatzResearch.WordTrace tailWord_4346656 prefixEnd_4346656 2231923767749450922110099 := by
  unfold tailWord_4346656
  simp only [CollatzResearch.WordTrace]
  refine ⟨79267784270407568294213911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105690379027210091058951881 79267784270407568294213911)
  ·
    refine ⟨118901676405611352441320867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79267784270407568294213911 118901676405611352441320867)
    ·
      refine ⟨178352514608417028661981301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118901676405611352441320867 178352514608417028661981301)
      ·
        refine ⟨16720548244539096437060747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178352514608417028661981301 16720548244539096437060747)
        ·
          refine ⟨25080822366808644655591121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16720548244539096437060747 25080822366808644655591121)
          ·
            refine ⟨18810616775106483491693341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25080822366808644655591121 18810616775106483491693341)
            ·
              refine ⟨7053981290664931309385003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18810616775106483491693341 7053981290664931309385003)
              ·
                refine ⟨10580971935997396964077505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053981290664931309385003 10580971935997396964077505)
                ·
                  refine ⟨7935728951998047723058129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10580971935997396964077505 7935728951998047723058129)
                  ·
                    refine ⟨5951796713998535792293597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7935728951998047723058129 5951796713998535792293597)
                    ·
                      refine ⟨2231923767749450922110099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5951796713998535792293597 2231923767749450922110099)
                      ·
                        rfl

theorem cell23_4346656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4346656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346656 prefixEnd_4346656 := by exact prefixLift 4346656
  have htrace : WordTrace (prefixWord ++ tailWord_4346656) baseStart_4346656 baseEnd_4346656 := by
    simpa [prefixWord, tailWord_4346656, baseEnd_4346656] using wordTrace_append hprefix tailTrace_4346656
  have hstable : (prefixWord ++ tailWord_4346656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346656).length < 2 ^ (prefixWord ++ tailWord_4346656).sum := by decide
  have hdescent : baseEnd_4346656 < baseStart_4346656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346676 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 8]
def baseStart_4346676 : Nat := 118140960795 + 4346676 * 2 ^ 59
def prefixEnd_4346676 : Nat := 4983230072969 + 3 ^ 40 * 4346676 * 2
def baseEnd_4346676 : Nat := 247992670818060093762223

theorem tailTrace_4346676 : CollatzResearch.WordTrace tailWord_4346676 prefixEnd_4346676 247992670818060093762223 := by
  unfold tailWord_4346676
  simp only [CollatzResearch.WordTrace]
  refine ⟨79268149000371340002077941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105690865333828453336103921 79268149000371340002077941)
  ·
    refine ⟨7431388968784813125194807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79268149000371340002077941 7431388968784813125194807)
    ·
      refine ⟨11147083453177219687792211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7431388968784813125194807 11147083453177219687792211)
      ·
        refine ⟨16720625179765829531688317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11147083453177219687792211 16720625179765829531688317)
        ·
          refine ⟨6270234442412186074383119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16720625179765829531688317 6270234442412186074383119)
          ·
            refine ⟨9405351663618279111574679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6270234442412186074383119 9405351663618279111574679)
            ·
              refine ⟨14108027495427418667362019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9405351663618279111574679 14108027495427418667362019)
              ·
                refine ⟨21162041243141128001043029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14108027495427418667362019 21162041243141128001043029)
                ·
                  refine ⟨247992670818060093762223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21162041243141128001043029 247992670818060093762223)
                  ·
                    rfl

theorem cell23_4346676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_4346676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346676 prefixEnd_4346676 := by exact prefixLift 4346676
  have htrace : WordTrace (prefixWord ++ tailWord_4346676) baseStart_4346676 baseEnd_4346676 := by
    simpa [prefixWord, tailWord_4346676, baseEnd_4346676] using wordTrace_append hprefix tailTrace_4346676
  have hstable : (prefixWord ++ tailWord_4346676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346676).length < 2 ^ (prefixWord ++ tailWord_4346676).sum := by decide
  have hdescent : baseEnd_4346676 < baseStart_4346676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346706 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_4346706 : Nat := 118140960795 + 4346706 * 2 ^ 59
def prefixEnd_4346706 : Nat := 4983230072969 + 3 ^ 40 * 4346706 * 2
def baseEnd_4346706 : Nat := 743983147260725242161623

theorem tailTrace_4346706 : CollatzResearch.WordTrace tailWord_4346706 prefixEnd_4346706 743983147260725242161623 := by
  unfold tailWord_4346706
  simp only [CollatzResearch.WordTrace]
  refine ⟨39634348047658498781936993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105691594793755996751831981 39634348047658498781936993)
  ·
    refine ⟨29725761035743874086452745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39634348047658498781936993 29725761035743874086452745)
    ·
      refine ⟨22294320776807905564839559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29725761035743874086452745 22294320776807905564839559)
      ·
        refine ⟨33441481165211858347259339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22294320776807905564839559 33441481165211858347259339)
        ·
          refine ⟨50162221747817787520889009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33441481165211858347259339 50162221747817787520889009)
          ·
            refine ⟨37621666310863340640666757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50162221747817787520889009 37621666310863340640666757)
            ·
              refine ⟨7054062433286876370125017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37621666310863340640666757 7054062433286876370125017)
              ·
                refine ⟨5290546824965157277593763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7054062433286876370125017 5290546824965157277593763)
                ·
                  refine ⟨7935820237447735916390645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5290546824965157277593763 7935820237447735916390645)
                  ·
                    refine ⟨743983147260725242161623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7935820237447735916390645 743983147260725242161623)
                    ·
                      rfl

theorem cell23_4346706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_4346706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346706 prefixEnd_4346706 := by exact prefixLift 4346706
  have htrace : WordTrace (prefixWord ++ tailWord_4346706) baseStart_4346706 baseEnd_4346706 := by
    simpa [prefixWord, tailWord_4346706, baseEnd_4346706] using wordTrace_append hprefix tailTrace_4346706
  have hstable : (prefixWord ++ tailWord_4346706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346706).length < 2 ^ (prefixWord ++ tailWord_4346706).sum := by decide
  have hdescent : baseEnd_4346706 < baseStart_4346706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346719 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 6, 4]
def baseStart_4346719 : Nat := 118140960795 + 4346719 * 2 ^ 59
def prefixEnd_4346719 : Nat := 4983230072969 + 3 ^ 40 * 4346719 * 2
def baseEnd_4346719 : Nat := 743985372343561391874103

theorem tailTrace_4346719 : CollatzResearch.WordTrace tailWord_4346719 prefixEnd_4346719 743985372343561391874103 := by
  unfold tailWord_4346719
  simp only [CollatzResearch.WordTrace]
  refine ⟨158537866339586898347971211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105691910893057932231980807 158537866339586898347971211)
  ·
    refine ⟨237806799509380347521956817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158537866339586898347971211 237806799509380347521956817)
    ·
      refine ⟨178355099632035260641467613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237806799509380347521956817 178355099632035260641467613)
      ·
        refine ⟨66883162362013222740550355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178355099632035260641467613 66883162362013222740550355)
        ·
          refine ⟨100324743543019834110825533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66883162362013222740550355 100324743543019834110825533)
          ·
            refine ⟨37621778828632437791559575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100324743543019834110825533 37621778828632437791559575)
            ·
              refine ⟨56432668242948656687339363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37621778828632437791559575 56432668242948656687339363)
              ·
                refine ⟨84649002364422985031009045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56432668242948656687339363 84649002364422985031009045)
                ·
                  refine ⟨3967921985832327423328549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84649002364422985031009045 3967921985832327423328549)
                  ·
                    refine ⟨743985372343561391874103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3967921985832327423328549 743985372343561391874103)
                    ·
                      rfl

theorem cell23_4346719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_4346719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346719 prefixEnd_4346719 := by exact prefixLift 4346719
  have htrace : WordTrace (prefixWord ++ tailWord_4346719) baseStart_4346719 baseEnd_4346719 := by
    simpa [prefixWord, tailWord_4346719, baseEnd_4346719] using wordTrace_append hprefix tailTrace_4346719
  have hstable : (prefixWord ++ tailWord_4346719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346719).length < 2 ^ (prefixWord ++ tailWord_4346719).sum := by decide
  have hdescent : baseEnd_4346719 < baseStart_4346719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346729 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_4346729 : Nat := 118140960795 + 4346729 * 2 ^ 59
def prefixEnd_4346729 : Nat := 4983230072969 + 3 ^ 40 * 4346729 * 2
def baseEnd_4346729 : Nat := 2231961251837229136497263

theorem tailTrace_4346729 : CollatzResearch.WordTrace tailWord_4346729 prefixEnd_4346729 2231961251837229136497263 := by
  unfold tailWord_4346729
  simp only [CollatzResearch.WordTrace]
  refine ⟨158538231069550670055835241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105692154046367113370556827 158538231069550670055835241)
  ·
    refine ⟨118903673302163002541876431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158538231069550670055835241 118903673302163002541876431)
    ·
      refine ⟨178355509953244503812814647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118903673302163002541876431 178355509953244503812814647)
      ·
        refine ⟨267533264929866755719221971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178355509953244503812814647 267533264929866755719221971)
        ·
          refine ⟨401299897394800133578832957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267533264929866755719221971 401299897394800133578832957)
          ·
            refine ⟨150487461523050050092062359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401299897394800133578832957 150487461523050050092062359)
            ·
              refine ⟨225731192284575075138093539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150487461523050050092062359 225731192284575075138093539)
              ·
                refine ⟨338596788426862612707140309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225731192284575075138093539 338596788426862612707140309)
                ·
                  refine ⟨7935862228754592485323601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 338596788426862612707140309 7935862228754592485323601)
                  ·
                    refine ⟨5951896671565944363992701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7935862228754592485323601 5951896671565944363992701)
                    ·
                      refine ⟨2231961251837229136497263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5951896671565944363992701 2231961251837229136497263)
                      ·
                        rfl

theorem cell23_4346729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_4346729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346729 prefixEnd_4346729 := by exact prefixLift 4346729
  have htrace : WordTrace (prefixWord ++ tailWord_4346729) baseStart_4346729 baseEnd_4346729 := by
    simpa [prefixWord, tailWord_4346729, baseEnd_4346729] using wordTrace_append hprefix tailTrace_4346729
  have hstable : (prefixWord ++ tailWord_4346729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346729).length < 2 ^ (prefixWord ++ tailWord_4346729).sum := by decide
  have hdescent : baseEnd_4346729 < baseStart_4346729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346780 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4346780 : Nat := 118140960795 + 4346780 * 2 ^ 59
def prefixEnd_4346780 : Nat := 4983230072969 + 3 ^ 40 * 4346780 * 2
def baseEnd_4346780 : Nat := 2231987439350608436959529

theorem tailTrace_4346780 : CollatzResearch.WordTrace tailWord_4346780 prefixEnd_4346780 2231987439350608436959529 := by
  unfold tailWord_4346780
  simp only [CollatzResearch.WordTrace]
  refine ⟨79270045596182952882970897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105693394128243937177294529 79270045596182952882970897)
  ·
    refine ⟨59452534197137214662228173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79270045596182952882970897 59452534197137214662228173)
    ·
      refine ⟨22294700323926455498335565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59452534197137214662228173 22294700323926455498335565)
      ·
        refine ⟨8360512621472420811875837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22294700323926455498335565 8360512621472420811875837)
        ·
          refine ⟨3135192233052157804453439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8360512621472420811875837 3135192233052157804453439)
          ·
            refine ⟨4702788349578236706680159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135192233052157804453439 4702788349578236706680159)
            ·
              refine ⟨7054182524367355060020239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702788349578236706680159 7054182524367355060020239)
              ·
                refine ⟨10581273786551032590030359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7054182524367355060020239 10581273786551032590030359)
                ·
                  refine ⟨15871910679826548885045539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10581273786551032590030359 15871910679826548885045539)
                  ·
                    refine ⟨23807866019739823327568309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15871910679826548885045539 23807866019739823327568309)
                    ·
                      refine ⟨2231987439350608436959529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23807866019739823327568309 2231987439350608436959529)
                      ·
                        rfl

theorem cell23_4346780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4346780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346780 prefixEnd_4346780 := by exact prefixLift 4346780
  have htrace : WordTrace (prefixWord ++ tailWord_4346780) baseStart_4346780 baseEnd_4346780 := by
    simpa [prefixWord, tailWord_4346780, baseEnd_4346780] using wordTrace_append hprefix tailTrace_4346780
  have hstable : (prefixWord ++ tailWord_4346780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346780).length < 2 ^ (prefixWord ++ tailWord_4346780).sum := by decide
  have hdescent : baseEnd_4346780 < baseStart_4346780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346793 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 3]
def baseStart_4346793 : Nat := 118140960795 + 4346793 * 2 ^ 59
def prefixEnd_4346793 : Nat := 4983230072969 + 3 ^ 40 * 4346793 * 2
def baseEnd_4346793 : Nat := 2231994114599116886096969

theorem tailTrace_4346793 : CollatzResearch.WordTrace tailWord_4346793 prefixEnd_4346793 2231994114599116886096969 := by
  unfold tailWord_4346793
  simp only [CollatzResearch.WordTrace]
  refine ⟨158540565341318808986165033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105693710227545872657443355 158540565341318808986165033)
  ·
    refine ⟨118905424005989106739623775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158540565341318808986165033 118905424005989106739623775)
    ·
      refine ⟨178358136008983660109435663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118905424005989106739623775 178358136008983660109435663)
      ·
        refine ⟨267537204013475490164153495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178358136008983660109435663 267537204013475490164153495)
        ·
          refine ⟨401305806020213235246230243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267537204013475490164153495 401305806020213235246230243)
          ·
            refine ⟨601958709030319852869345365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401305806020213235246230243 601958709030319852869345365)
            ·
              refine ⟨7054203621449060775812641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 601958709030319852869345365 7054203621449060775812641)
              ·
                refine ⟨5290652716086795581859481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7054203621449060775812641 5290652716086795581859481)
                ·
                  refine ⟨3967989537065096686394611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5290652716086795581859481 3967989537065096686394611)
                  ·
                    refine ⟨5951984305597645029591917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3967989537065096686394611 5951984305597645029591917)
                    ·
                      refine ⟨2231994114599116886096969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5951984305597645029591917 2231994114599116886096969)
                      ·
                        rfl

theorem cell23_4346793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_4346793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346793 prefixEnd_4346793 := by exact prefixLift 4346793
  have htrace : WordTrace (prefixWord ++ tailWord_4346793) baseStart_4346793 baseEnd_4346793 := by
    simpa [prefixWord, tailWord_4346793, baseEnd_4346793] using wordTrace_append hprefix tailTrace_4346793
  have hstable : (prefixWord ++ tailWord_4346793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346793).length < 2 ^ (prefixWord ++ tailWord_4346793).sum := by decide
  have hdescent : baseEnd_4346793 < baseStart_4346793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346809 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_4346809 : Nat := 118140960795 + 4346809 * 2 ^ 59
def prefixEnd_4346809 : Nat := 4983230072969 + 3 ^ 40 * 4346809 * 2
def baseEnd_4346809 : Nat := 744000776763196274498965

theorem tailTrace_4346809 : CollatzResearch.WordTrace tailWord_4346809 prefixEnd_4346809 744000776763196274498965 := by
  unfold tailWord_4346809
  simp only [CollatzResearch.WordTrace]
  refine ⟨158541148909260843718747481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105694099272840562479164987 158541148909260843718747481)
  ·
    refine ⟨118905861681945632789060611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158541148909260843718747481 118905861681945632789060611)
    ·
      refine ⟨178358792522918449183590917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118905861681945632789060611 178358792522918449183590917)
      ·
        refine ⟨33442273598047209221923297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178358792522918449183590917 33442273598047209221923297)
        ·
          refine ⟨25081705198535406916442473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33442273598047209221923297 25081705198535406916442473)
          ·
            refine ⟨18811278898901555187331855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25081705198535406916442473 18811278898901555187331855)
            ·
              refine ⟨28216918348352332780997783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18811278898901555187331855 28216918348352332780997783)
              ·
                refine ⟨42325377522528499171496675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28216918348352332780997783 42325377522528499171496675)
                ·
                  refine ⟨63488066283792748757245013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42325377522528499171496675 63488066283792748757245013)
                  ·
                    refine ⟨744000776763196274498965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63488066283792748757245013 744000776763196274498965)
                    ·
                      rfl

theorem cell23_4346809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_4346809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346809 prefixEnd_4346809 := by exact prefixLift 4346809
  have htrace : WordTrace (prefixWord ++ tailWord_4346809) baseStart_4346809 baseEnd_4346809 := by
    simpa [prefixWord, tailWord_4346809, baseEnd_4346809] using wordTrace_append hprefix tailTrace_4346809
  have hstable : (prefixWord ++ tailWord_4346809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346809).length < 2 ^ (prefixWord ++ tailWord_4346809).sum := by decide
  have hdescent : baseEnd_4346809 < baseStart_4346809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346833 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 4, 2, 2]
def baseStart_4346833 : Nat := 118140960795 + 4346833 * 2 ^ 59
def prefixEnd_4346833 : Nat := 4983230072969 + 3 ^ 40 * 4346833 * 2
def baseEnd_4346833 : Nat := 2232014653825296729596785

theorem tailTrace_4346833 : CollatzResearch.WordTrace tailWord_4346833 prefixEnd_4346833 2232014653825296729596785 := by
  unfold tailWord_4346833
  simp only [CollatzResearch.WordTrace]
  refine ⟨158542024261173895817621153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105694682840782597211747435 158542024261173895817621153)
  ·
    refine ⟨118906518195880421863215865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158542024261173895817621153 118906518195880421863215865)
    ·
      refine ⟨89179888646910316397411899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118906518195880421863215865 89179888646910316397411899)
      ·
        refine ⟨133769832970365474596117849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89179888646910316397411899 133769832970365474596117849)
        ·
          refine ⟨100327374727774105947088387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133769832970365474596117849 100327374727774105947088387)
          ·
            refine ⟨150491062091661158920632581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100327374727774105947088387 150491062091661158920632581)
            ·
              refine ⟨28217074142186467297618609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150491062091661158920632581 28217074142186467297618609)
              ·
                refine ⟨21162805606639850473213957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28217074142186467297618609 21162805606639850473213957)
                ·
                  refine ⟨3968026051244971963727617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21162805606639850473213957 3968026051244971963727617)
                  ·
                    refine ⟨2976019538433728972795713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3968026051244971963727617 2976019538433728972795713)
                    ·
                      refine ⟨2232014653825296729596785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976019538433728972795713 2232014653825296729596785)
                      ·
                        rfl

theorem cell23_4346833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_4346833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346833 prefixEnd_4346833 := by exact prefixLift 4346833
  have htrace : WordTrace (prefixWord ++ tailWord_4346833) baseStart_4346833 baseEnd_4346833 := by
    simpa [prefixWord, tailWord_4346833, baseEnd_4346833] using wordTrace_append hprefix tailTrace_4346833
  have hstable : (prefixWord ++ tailWord_4346833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346833).length < 2 ^ (prefixWord ++ tailWord_4346833).sum := by decide
  have hdescent : baseEnd_4346833 < baseStart_4346833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346879 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_4346879 : Nat := 118140960795 + 4346879 * 2 ^ 59
def prefixEnd_4346879 : Nat := 4983230072969 + 3 ^ 40 * 4346879 * 2
def baseEnd_4346879 : Nat := 2232038273935403549621573

theorem tailTrace_4346879 : CollatzResearch.WordTrace tailWord_4346879 prefixEnd_4346879 2232038273935403549621573 := by
  unfold tailWord_4346879
  simp only [CollatzResearch.WordTrace]
  refine ⟨158543702019007245673795691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105695801346004830449197127 158543702019007245673795691)
  ·
    refine ⟨237815553028510868510693537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158543702019007245673795691 237815553028510868510693537)
    ·
      refine ⟨178361664771383151383020153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237815553028510868510693537 178361664771383151383020153)
      ·
        refine ⟨133771248578537363537265115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178361664771383151383020153 133771248578537363537265115)
        ·
          refine ⟨200656872867806045305897673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133771248578537363537265115 200656872867806045305897673)
          ·
            refine ⟨150492654650854533979423255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200656872867806045305897673 150492654650854533979423255)
            ·
              refine ⟨225738981976281800969134883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150492654650854533979423255 225738981976281800969134883)
              ·
                refine ⟨338608472964422701453702325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225738981976281800969134883 338608472964422701453702325)
                ·
                  refine ⟨31744544340414628261284593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338608472964422701453702325 31744544340414628261284593)
                  ·
                    refine ⟨23808408255310971195963445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31744544340414628261284593 23808408255310971195963445)
                    ·
                      refine ⟨2232038273935403549621573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23808408255310971195963445 2232038273935403549621573)
                      ·
                        rfl

theorem cell23_4346879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_4346879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346879 prefixEnd_4346879 := by exact prefixLift 4346879
  have htrace : WordTrace (prefixWord ++ tailWord_4346879) baseStart_4346879 baseEnd_4346879 := by
    simpa [prefixWord, tailWord_4346879, baseEnd_4346879] using wordTrace_append hprefix tailTrace_4346879
  have hstable : (prefixWord ++ tailWord_4346879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346879).length < 2 ^ (prefixWord ++ tailWord_4346879).sum := by decide
  have hdescent : baseEnd_4346879 < baseStart_4346879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346890 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_4346890 : Nat := 118140960795 + 4346890 * 2 ^ 59
def prefixEnd_4346890 : Nat := 4983230072969 + 3 ^ 40 * 4346890 * 2
def baseEnd_4346890 : Nat := 248004880246955889620447

theorem tailTrace_4346890 : CollatzResearch.WordTrace tailWord_4346890 prefixEnd_4346890 248004880246955889620447 := by
  unfold tailWord_4346890
  simp only [CollatzResearch.WordTrace]
  refine ⟨39636025805491848638111531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105696068814644929701630749 39636025805491848638111531)
  ·
    refine ⟨59454038708237772957167297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39636025805491848638111531 59454038708237772957167297)
    ·
      refine ⟨44590529031178329717875473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59454038708237772957167297 44590529031178329717875473)
      ·
        refine ⟨33442896773383747288406605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44590529031178329717875473 33442896773383747288406605)
        ·
          refine ⟨12541086290018905233152477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33442896773383747288406605 12541086290018905233152477)
          ·
            refine ⟨4702907358757089462432179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12541086290018905233152477 4702907358757089462432179)
            ·
              refine ⟨7054361038135634193648269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702907358757089462432179 7054361038135634193648269)
              ·
                refine ⟨2645385389300862822618101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7054361038135634193648269 2645385389300862822618101)
                ·
                  refine ⟨248004880246955889620447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2645385389300862822618101 248004880246955889620447)
                  ·
                    rfl

theorem cell23_4346890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_4346890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346890 prefixEnd_4346890 := by exact prefixLift 4346890
  have htrace : WordTrace (prefixWord ++ tailWord_4346890) baseStart_4346890 baseEnd_4346890 := by
    simpa [prefixWord, tailWord_4346890, baseEnd_4346890] using wordTrace_append hprefix tailTrace_4346890
  have hstable : (prefixWord ++ tailWord_4346890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346890).length < 2 ^ (prefixWord ++ tailWord_4346890).sum := by decide
  have hdescent : baseEnd_4346890 < baseStart_4346890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346903 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 2, 5]
def baseStart_4346903 : Nat := 118140960795 + 4346903 * 2 ^ 59
def prefixEnd_4346903 : Nat := 4983230072969 + 3 ^ 40 * 4346903 * 2
def baseEnd_4346903 : Nat := 744016865823703818573821

theorem tailTrace_4346903 : CollatzResearch.WordTrace tailWord_4346903 prefixEnd_4346903 744016865823703818573821 := by
  unfold tailWord_4346903
  simp only [CollatzResearch.WordTrace]
  refine ⟨158544577370920297772669363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105696384913946865181779575 158544577370920297772669363)
  ·
    refine ⟨237816866056380446659004045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158544577370920297772669363 237816866056380446659004045)
    ·
      refine ⟨89181324771142667497126517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237816866056380446659004045 89181324771142667497126517)
      ·
        refine ⟨8360749197294625077855611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89181324771142667497126517 8360749197294625077855611)
        ·
          refine ⟨12541123795941937616783417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8360749197294625077855611 12541123795941937616783417)
          ·
            refine ⟨9405842846956453212587563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12541123795941937616783417 9405842846956453212587563)
            ·
              refine ⟨14108764270434679818881345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9405842846956453212587563 14108764270434679818881345)
              ·
                refine ⟨10581573202826009864161009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14108764270434679818881345 10581573202826009864161009)
                ·
                  refine ⟨7936179902119507398120757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10581573202826009864161009 7936179902119507398120757)
                  ·
                    refine ⟨744016865823703818573821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7936179902119507398120757 744016865823703818573821)
                    ·
                      rfl

theorem cell23_4346903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_4346903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346903 prefixEnd_4346903 := by exact prefixLift 4346903
  have htrace : WordTrace (prefixWord ++ tailWord_4346903) baseStart_4346903 baseEnd_4346903 := by
    simpa [prefixWord, tailWord_4346903, baseEnd_4346903] using wordTrace_append hprefix tailTrace_4346903
  have hstable : (prefixWord ++ tailWord_4346903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346903).length < 2 ^ (prefixWord ++ tailWord_4346903).sum := by decide
  have hdescent : baseEnd_4346903 < baseStart_4346903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346939 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_4346939 : Nat := 118140960795 + 4346939 * 2 ^ 59
def prefixEnd_4346939 : Nat := 4983230072969 + 3 ^ 40 * 4346939 * 2
def baseEnd_4346939 : Nat := 2232069082774673314871297

theorem tailTrace_4346939 : CollatzResearch.WordTrace tailWord_4346939 prefixEnd_4346939 2232069082774673314871297 := by
  unfold tailWord_4346939
  simp only [CollatzResearch.WordTrace]
  refine ⟨158545890398789875920979871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105697260265859917280653247 158545890398789875920979871)
  ·
    refine ⟨237818835598184813881469807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158545890398789875920979871 237818835598184813881469807)
    ·
      refine ⟨356728253397277220822204711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237818835598184813881469807 356728253397277220822204711)
      ·
        refine ⟨535092380095915831233307067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356728253397277220822204711 535092380095915831233307067)
        ·
          refine ⟨802638570143873746849960601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535092380095915831233307067 802638570143873746849960601)
          ·
            refine ⟨601978927607905310137470451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802638570143873746849960601 601978927607905310137470451)
            ·
              refine ⟨902968391411857965206205677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601978927607905310137470451 902968391411857965206205677)
              ·
                refine ⟨338613146779446736952327129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902968391411857965206205677 338613146779446736952327129)
                ·
                  refine ⟨253959860084585052714245347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338613146779446736952327129 253959860084585052714245347)
                  ·
                    refine ⟨380939790126877579071368021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253959860084585052714245347 380939790126877579071368021)
                    ·
                      refine ⟨2232069082774673314871297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 380939790126877579071368021 2232069082774673314871297)
                      ·
                        rfl

theorem cell23_4346939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_4346939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346939 prefixEnd_4346939 := by exact prefixLift 4346939
  have htrace : WordTrace (prefixWord ++ tailWord_4346939) baseStart_4346939 baseEnd_4346939 := by
    simpa [prefixWord, tailWord_4346939, baseEnd_4346939] using wordTrace_append hprefix tailTrace_4346939
  have hstable : (prefixWord ++ tailWord_4346939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346939).length < 2 ^ (prefixWord ++ tailWord_4346939).sum := by decide
  have hdescent : baseEnd_4346939 < baseStart_4346939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346974 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4346974 : Nat := 118140960795 + 4346974 * 2 ^ 59
def prefixEnd_4346974 : Nat := 4983230072969 + 3 ^ 40 * 4346974 * 2
def baseEnd_4346974 : Nat := 2232087054597580677933637

theorem tailTrace_4346974 : CollatzResearch.WordTrace tailWord_4346974 prefixEnd_4346974 2232087054597580677933637 := by
  unfold tailWord_4346974
  simp only [CollatzResearch.WordTrace]
  refine ⟨19818395869207884612312997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105698111302442051265669317 19818395869207884612312997)
  ·
    refine ⟨3715949225476478364808687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19818395869207884612312997 3715949225476478364808687)
    ·
      refine ⟨5573923838214717547213031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715949225476478364808687 5573923838214717547213031)
      ·
        refine ⟨8360885757322076320819547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573923838214717547213031 8360885757322076320819547)
        ·
          refine ⟨12541328635983114481229321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8360885757322076320819547 12541328635983114481229321)
          ·
            refine ⟨9405996476987335860921991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12541328635983114481229321 9405996476987335860921991)
            ·
              refine ⟨14108994715481003791382987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9405996476987335860921991 14108994715481003791382987)
              ·
                refine ⟨21163492073221505687074481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14108994715481003791382987 21163492073221505687074481)
                ·
                  refine ⟨15872619054916129265305861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21163492073221505687074481 15872619054916129265305861)
                  ·
                    refine ⟨2976116072796774237244849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15872619054916129265305861 2976116072796774237244849)
                    ·
                      refine ⟨2232087054597580677933637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976116072796774237244849 2232087054597580677933637)
                      ·
                        rfl

theorem cell23_4346974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4346974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346974 prefixEnd_4346974 := by exact prefixLift 4346974
  have htrace : WordTrace (prefixWord ++ tailWord_4346974) baseStart_4346974 baseEnd_4346974 := by
    simpa [prefixWord, tailWord_4346974, baseEnd_4346974] using wordTrace_append hprefix tailTrace_4346974
  have hstable : (prefixWord ++ tailWord_4346974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346974).length < 2 ^ (prefixWord ++ tailWord_4346974).sum := by decide
  have hdescent : baseEnd_4346974 < baseStart_4346974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346976 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_4346976 : Nat := 118140960795 + 4346976 * 2 ^ 59
def prefixEnd_4346976 : Nat := 4983230072969 + 3 ^ 40 * 4346976 * 2
def baseEnd_4346976 : Nat := 744029360519629890036209

theorem tailTrace_4346976 : CollatzResearch.WordTrace tailWord_4346976 prefixEnd_4346976 744029360519629890036209 := by
  unfold tailWord_4346976
  simp only [CollatzResearch.WordTrace]
  refine ⟨79273619949827915620038391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105698159933103887493384521 79273619949827915620038391)
  ·
    refine ⟨118910429924741873430057587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79273619949827915620038391 118910429924741873430057587)
    ·
      refine ⟨178365644887112810145086381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118910429924741873430057587 178365644887112810145086381)
      ·
        refine ⟨66887116832667303804407393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178365644887112810145086381 66887116832667303804407393)
        ·
          refine ⟨50165337624500477853305545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66887116832667303804407393 50165337624500477853305545)
          ·
            refine ⟨37624003218375358389979159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50165337624500477853305545 37624003218375358389979159)
            ·
              refine ⟨56436004827563037584968739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37624003218375358389979159 56436004827563037584968739)
              ·
                refine ⟨84654007241344556377453109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56436004827563037584968739 84654007241344556377453109)
                ·
                  refine ⟨7936313178876052160386229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84654007241344556377453109 7936313178876052160386229)
                  ·
                    refine ⟨744029360519629890036209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7936313178876052160386229 744029360519629890036209)
                    ·
                      rfl

theorem cell23_4346976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_4346976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346976 prefixEnd_4346976 := by exact prefixLift 4346976
  have htrace : WordTrace (prefixWord ++ tailWord_4346976) baseStart_4346976 baseEnd_4346976 := by
    simpa [prefixWord, tailWord_4346976, baseEnd_4346976] using wordTrace_append hprefix tailTrace_4346976
  have hstable : (prefixWord ++ tailWord_4346976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346976).length < 2 ^ (prefixWord ++ tailWord_4346976).sum := by decide
  have hdescent : baseEnd_4346976 < baseStart_4346976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4346990 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_4346990 : Nat := 118140960795 + 4346990 * 2 ^ 59
def prefixEnd_4346990 : Nat := 4983230072969 + 3 ^ 40 * 4346990 * 2
def baseEnd_4346990 : Nat := 2232095270288052615333563

theorem tailTrace_4346990 : CollatzResearch.WordTrace tailWord_4346990 prefixEnd_4346990 2232095270288052615333563 := by
  unfold tailWord_4346990
  simp only [CollatzResearch.WordTrace]
  refine ⟨19818468815200638953885803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105698500347736741087390949 19818468815200638953885803)
  ·
    refine ⟨29727703222800958430828705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19818468815200638953885803 29727703222800958430828705)
    ·
      refine ⟨22295777417100718823121529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29727703222800958430828705 22295777417100718823121529)
      ·
        refine ⟨16721833062825539117341147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22295777417100718823121529 16721833062825539117341147)
        ·
          refine ⟨25082749594238308676011721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16721833062825539117341147 25082749594238308676011721)
          ·
            refine ⟨18812062195678731507008791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25082749594238308676011721 18812062195678731507008791)
            ·
              refine ⟨28218093293518097260513187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18812062195678731507008791 28218093293518097260513187)
              ·
                refine ⟨42327139940277145890769781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28218093293518097260513187 42327139940277145890769781)
                ·
                  refine ⟨3968169369400982427259667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42327139940277145890769781 3968169369400982427259667)
                  ·
                    refine ⟨5952254054101473640889501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3968169369400982427259667 5952254054101473640889501)
                    ·
                      refine ⟨2232095270288052615333563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952254054101473640889501 2232095270288052615333563)
                      ·
                        rfl

theorem cell23_4346990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_4346990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4346990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4346990 prefixEnd_4346990 := by exact prefixLift 4346990
  have htrace : WordTrace (prefixWord ++ tailWord_4346990) baseStart_4346990 baseEnd_4346990 := by
    simpa [prefixWord, tailWord_4346990, baseEnd_4346990] using wordTrace_append hprefix tailTrace_4346990
  have hstable : (prefixWord ++ tailWord_4346990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4346990).length < 2 ^ (prefixWord ++ tailWord_4346990).sum := by decide
  have hdescent : baseEnd_4346990 < baseStart_4346990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4346990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347000 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 2, 3, 2]
def baseStart_4347000 : Nat := 118140960795 + 4347000 * 2 ^ 59
def prefixEnd_4347000 : Nat := 4983230072969 + 3 ^ 40 * 4347000 * 2
def baseEnd_4347000 : Nat := 2232100405094597576208517

theorem tailTrace_4347000 : CollatzResearch.WordTrace tailWord_4347000 prefixEnd_4347000 2232100405094597576208517 := by
  unfold tailWord_4347000
  simp only [CollatzResearch.WordTrace]
  refine ⟨79274057625784441669475227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105698743501045922225966969 79274057625784441669475227)
  ·
    refine ⟨118911086438676662504212841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79274057625784441669475227 118911086438676662504212841)
    ·
      refine ⟨89183314829007496878159631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118911086438676662504212841 89183314829007496878159631)
      ·
        refine ⟨133774972243511245317239447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89183314829007496878159631 133774972243511245317239447)
        ·
          refine ⟨200662458365266867975859171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133774972243511245317239447 200662458365266867975859171)
          ·
            refine ⟨300993687547900301963788757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200662458365266867975859171 300993687547900301963788757)
            ·
              refine ⟨7054539551903913327276299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 300993687547900301963788757 7054539551903913327276299)
              ·
                refine ⟨10581809327855869990914449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7054539551903913327276299 10581809327855869990914449)
                ·
                  refine ⟨7936356995891902493185837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10581809327855869990914449 7936356995891902493185837)
                  ·
                    refine ⟨2976133873459463434944689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7936356995891902493185837 2976133873459463434944689)
                    ·
                      refine ⟨2232100405094597576208517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976133873459463434944689 2232100405094597576208517)
                      ·
                        rfl

theorem cell23_4347000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_4347000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347000 prefixEnd_4347000 := by exact prefixLift 4347000
  have htrace : WordTrace (prefixWord ++ tailWord_4347000) baseStart_4347000 baseEnd_4347000 := by
    simpa [prefixWord, tailWord_4347000, baseEnd_4347000] using wordTrace_append hprefix tailTrace_4347000
  have hstable : (prefixWord ++ tailWord_4347000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347000).length < 2 ^ (prefixWord ++ tailWord_4347000).sum := by decide
  have hdescent : baseEnd_4347000 < baseStart_4347000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347047 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4347047 : Nat := 118140960795 + 4347047 * 2 ^ 59
def prefixEnd_4347047 : Nat := 4983230072969 + 3 ^ 40 * 4347047 * 2
def baseEnd_4347047 : Nat := 2232124538685358892320801

theorem tailTrace_4347047 : CollatzResearch.WordTrace tailWord_4347047 prefixEnd_4347047 2232124538685358892320801 := by
  unfold tailWord_4347047
  simp only [CollatzResearch.WordTrace]
  refine ⟨158549829482398610365911395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105699886321599073577274263 158549829482398610365911395)
  ·
    refine ⟨237824744223597915548867093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158549829482398610365911395 237824744223597915548867093)
    ·
      refine ⟨11148034885481152291353145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 237824744223597915548867093 11148034885481152291353145)
      ·
        refine ⟨8361026164110864218514859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11148034885481152291353145 8361026164110864218514859)
        ·
          refine ⟨12541539246166296327772289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8361026164110864218514859 12541539246166296327772289)
          ·
            refine ⟨9406154434624722245829217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12541539246166296327772289 9406154434624722245829217)
            ·
              refine ⟨7054615825968541684371913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9406154434624722245829217 7054615825968541684371913)
              ·
                refine ⟨5290961869476406263278935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7054615825968541684371913 5290961869476406263278935)
                ·
                  refine ⟨7936442804214609394918403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5290961869476406263278935 7936442804214609394918403)
                  ·
                    refine ⟨11904664206321914092377605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7936442804214609394918403 11904664206321914092377605)
                    ·
                      refine ⟨2232124538685358892320801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11904664206321914092377605 2232124538685358892320801)
                      ·
                        rfl

theorem cell23_4347047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4347047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347047 prefixEnd_4347047 := by exact prefixLift 4347047
  have htrace : WordTrace (prefixWord ++ tailWord_4347047) baseStart_4347047 baseEnd_4347047 := by
    simpa [prefixWord, tailWord_4347047, baseEnd_4347047] using wordTrace_append hprefix tailTrace_4347047
  have hstable : (prefixWord ++ tailWord_4347047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347047).length < 2 ^ (prefixWord ++ tailWord_4347047).sum := by decide
  have hdescent : baseEnd_4347047 < baseStart_4347047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347063 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_4347063 : Nat := 118140960795 + 4347063 * 2 ^ 59
def prefixEnd_4347063 : Nat := 4983230072969 + 3 ^ 40 * 4347063 * 2
def baseEnd_4347063 : Nat := 2232132754375830829720727

theorem tailTrace_4347063 : CollatzResearch.WordTrace tailWord_4347063 prefixEnd_4347063 2232132754375830829720727 := by
  unfold tailWord_4347063
  simp only [CollatzResearch.WordTrace]
  refine ⟨158550413050340645098493843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105700275366893763398995895 158550413050340645098493843)
  ·
    refine ⟨237825619575510967647740765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158550413050340645098493843 237825619575510967647740765)
    ·
      refine ⟨89184607340816612867902787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237825619575510967647740765 89184607340816612867902787)
      ·
        refine ⟨133776911011224919301854181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89184607340816612867902787 133776911011224919301854181)
        ·
          refine ⟨25083170814604672369097659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133776911011224919301854181 25083170814604672369097659)
          ·
            refine ⟨37624756221907008553646489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25083170814604672369097659 37624756221907008553646489)
            ·
              refine ⟨28218567166430256415234867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37624756221907008553646489 28218567166430256415234867)
              ·
                refine ⟨42327850749645384622852301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28218567166430256415234867 42327850749645384622852301)
                ·
                  refine ⟨15872944031117019233569613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42327850749645384622852301 15872944031117019233569613)
                  ·
                    refine ⟨5952354011668882212588605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15872944031117019233569613 5952354011668882212588605)
                    ·
                      refine ⟨2232132754375830829720727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952354011668882212588605 2232132754375830829720727)
                      ·
                        rfl

theorem cell23_4347063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_4347063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347063 prefixEnd_4347063 := by exact prefixLift 4347063
  have htrace : WordTrace (prefixWord ++ tailWord_4347063) baseStart_4347063 baseEnd_4347063 := by
    simpa [prefixWord, tailWord_4347063, baseEnd_4347063] using wordTrace_append hprefix tailTrace_4347063
  have hstable : (prefixWord ++ tailWord_4347063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347063).length < 2 ^ (prefixWord ++ tailWord_4347063).sum := by decide
  have hdescent : baseEnd_4347063 < baseStart_4347063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347066 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_4347066 : Nat := 118140960795 + 4347066 * 2 ^ 59
def prefixEnd_4347066 : Nat := 4983230072969 + 3 ^ 40 * 4347066 * 2
def baseEnd_4347066 : Nat := 744044764939264772661071

theorem tailTrace_4347066 : CollatzResearch.WordTrace tailWord_4347066 prefixEnd_4347066 744044764939264772661071 := by
  unfold tailWord_4347066
  simp only [CollatzResearch.WordTrace]
  refine ⟨39637630617332444152713263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105700348312886517740568701 39637630617332444152713263)
  ·
    refine ⟨59456445925998666229069895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39637630617332444152713263 59456445925998666229069895)
    ·
      refine ⟨89184668888997999343604843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59456445925998666229069895 89184668888997999343604843)
      ·
        refine ⟨133777003333496999015407265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89184668888997999343604843 133777003333496999015407265)
        ·
          refine ⟨100332752500122749261555449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133777003333496999015407265 100332752500122749261555449)
          ·
            refine ⟨75249564375092061946166587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100332752500122749261555449 75249564375092061946166587)
            ·
              refine ⟨112874346562638092919249881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75249564375092061946166587 112874346562638092919249881)
              ·
                refine ⟨84655759921978569689437411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112874346562638092919249881 84655759921978569689437411)
                ·
                  refine ⟨126983639882967854534156117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84655759921978569689437411 126983639882967854534156117)
                  ·
                    refine ⟨744044764939264772661071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126983639882967854534156117 744044764939264772661071)
                    ·
                      rfl

theorem cell23_4347066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_4347066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347066 prefixEnd_4347066 := by exact prefixLift 4347066
  have htrace : WordTrace (prefixWord ++ tailWord_4347066) baseStart_4347066 baseEnd_4347066 := by
    simpa [prefixWord, tailWord_4347066, baseEnd_4347066] using wordTrace_append hprefix tailTrace_4347066
  have hstable : (prefixWord ++ tailWord_4347066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347066).length < 2 ^ (prefixWord ++ tailWord_4347066).sum := by decide
  have hdescent : baseEnd_4347066 < baseStart_4347066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347080 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_4347080 : Nat := 118140960795 + 4347080 * 2 ^ 59
def prefixEnd_4347080 : Nat := 4983230072969 + 3 ^ 40 * 4347080 * 2
def baseEnd_4347080 : Nat := 2232141483546957263208149

theorem tailTrace_4347080 : CollatzResearch.WordTrace tailWord_4347080 prefixEnd_4347080 2232141483546957263208149 := by
  unfold tailWord_4347080
  simp only [CollatzResearch.WordTrace]
  refine ⟨79275516545639528500931347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105700688727519371334575129 79275516545639528500931347)
  ·
    refine ⟨118913274818459292751397021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79275516545639528500931347 118913274818459292751397021)
    ·
      refine ⟨44592478056922234781773883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118913274818459292751397021 44592478056922234781773883)
      ·
        refine ⟨66888717085383352172660825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44592478056922234781773883 66888717085383352172660825)
        ·
          refine ⟨50166537814037514129495619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66888717085383352172660825 50166537814037514129495619)
          ·
            refine ⟨75249806721056271194243429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50166537814037514129495619 75249806721056271194243429)
            ·
              refine ⟨14109338760198050848920643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75249806721056271194243429 14109338760198050848920643)
              ·
                refine ⟨21164008140297076273380965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14109338760198050848920643 21164008140297076273380965)
                ·
                  refine ⟨3968251526305701801258931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21164008140297076273380965 3968251526305701801258931)
                  ·
                    refine ⟨5952377289458552701888397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3968251526305701801258931 5952377289458552701888397)
                    ·
                      refine ⟨2232141483546957263208149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952377289458552701888397 2232141483546957263208149)
                      ·
                        rfl

theorem cell23_4347080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_4347080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347080 prefixEnd_4347080 := by exact prefixLift 4347080
  have htrace : WordTrace (prefixWord ++ tailWord_4347080) baseStart_4347080 baseEnd_4347080 := by
    simpa [prefixWord, tailWord_4347080, baseEnd_4347080] using wordTrace_append hprefix tailTrace_4347080
  have hstable : (prefixWord ++ tailWord_4347080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347080).length < 2 ^ (prefixWord ++ tailWord_4347080).sum := by decide
  have hdescent : baseEnd_4347080 < baseStart_4347080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347101 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4347101 : Nat := 118140960795 + 4347101 * 2 ^ 59
def prefixEnd_4347101 : Nat := 4983230072969 + 3 ^ 40 * 4347101 * 2
def baseEnd_4347101 : Nat := 2232152266640701681045553

theorem tailTrace_4347101 : CollatzResearch.WordTrace tailWord_4347101 prefixEnd_4347101 2232152266640701681045553 := by
  unfold tailWord_4347101
  simp only [CollatzResearch.WordTrace]
  refine ⟨158551799024202977588377157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105701199349468651725584771 158551799024202977588377157)
  ·
    refine ⟨29728462317038058297820717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158551799024202977588377157 29728462317038058297820717)
    ·
      refine ⟨11148173368889271861682769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29728462317038058297820717 11148173368889271861682769)
      ·
        refine ⟨8361130026666953896262077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11148173368889271861682769 8361130026666953896262077)
        ·
          refine ⟨3135423760000107711098279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8361130026666953896262077 3135423760000107711098279)
          ·
            refine ⟨4703135640000161566647419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135423760000107711098279 4703135640000161566647419)
            ·
              refine ⟨7054703460000242349971129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703135640000161566647419 7054703460000242349971129)
              ·
                refine ⟨5291027595000181762478347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7054703460000242349971129 5291027595000181762478347)
                ·
                  refine ⟨7936541392500272643717521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291027595000181762478347 7936541392500272643717521)
                  ·
                    refine ⟨5952406044375204482788141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7936541392500272643717521 5952406044375204482788141)
                    ·
                      refine ⟨2232152266640701681045553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952406044375204482788141 2232152266640701681045553)
                      ·
                        rfl

theorem cell23_4347101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4347101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347101 prefixEnd_4347101 := by exact prefixLift 4347101
  have htrace : WordTrace (prefixWord ++ tailWord_4347101) baseStart_4347101 baseEnd_4347101 := by
    simpa [prefixWord, tailWord_4347101, baseEnd_4347101] using wordTrace_append hprefix tailTrace_4347101
  have hstable : (prefixWord ++ tailWord_4347101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347101).length < 2 ^ (prefixWord ++ tailWord_4347101).sum := by decide
  have hdescent : baseEnd_4347101 < baseStart_4347101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347123 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5]
def baseStart_4347123 : Nat := 118140960795 + 4347123 * 2 ^ 59
def prefixEnd_4347123 : Nat := 4983230072969 + 3 ^ 40 * 4347123 * 2
def baseEnd_4347123 : Nat := 2232163563215100594970451

theorem tailTrace_4347123 : CollatzResearch.WordTrace tailWord_4347123 prefixEnd_4347123 2232163563215100594970451 := by
  unfold tailWord_4347123
  simp only [CollatzResearch.WordTrace]
  refine ⟨158552601430123275345678023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105701734286748850230452015 158552601430123275345678023)
  ·
    refine ⟨237828902145184913018517035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158552601430123275345678023 237828902145184913018517035)
    ·
      refine ⟨356743353217777369527775553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237828902145184913018517035 356743353217777369527775553)
      ·
        refine ⟨267557514913333027145831665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356743353217777369527775553 267557514913333027145831665)
        ·
          refine ⟨200668136184999770359373749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267557514913333027145831665 200668136184999770359373749)
          ·
            refine ⟨18812637767343728471191289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200668136184999770359373749 18812637767343728471191289)
            ·
              refine ⟨14109478325507796353393467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18812637767343728471191289 14109478325507796353393467)
              ·
                refine ⟨21164217488261694530090201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14109478325507796353393467 21164217488261694530090201)
                ·
                  refine ⟨15873163116196270897567651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21164217488261694530090201 15873163116196270897567651)
                  ·
                    refine ⟨23809744674294406346351477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15873163116196270897567651 23809744674294406346351477)
                    ·
                      refine ⟨2232163563215100594970451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23809744674294406346351477 2232163563215100594970451)
                      ·
                        rfl

theorem cell23_4347123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_4347123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347123 prefixEnd_4347123 := by exact prefixLift 4347123
  have htrace : WordTrace (prefixWord ++ tailWord_4347123) baseStart_4347123 baseEnd_4347123 := by
    simpa [prefixWord, tailWord_4347123, baseEnd_4347123] using wordTrace_append hprefix tailTrace_4347123
  have hstable : (prefixWord ++ tailWord_4347123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347123).length < 2 ^ (prefixWord ++ tailWord_4347123).sum := by decide
  have hdescent : baseEnd_4347123 < baseStart_4347123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347140 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_4347140 : Nat := 118140960795 + 4347140 * 2 ^ 59
def prefixEnd_4347140 : Nat := 4983230072969 + 3 ^ 40 * 4347140 * 2
def baseEnd_4347140 : Nat := 2232172292386227028457873

theorem tailTrace_4347140 : CollatzResearch.WordTrace tailWord_4347140 prefixEnd_4347140 2232172292386227028457873 := by
  unfold tailWord_4347140
  simp only [CollatzResearch.WordTrace]
  refine ⟨79276610735530843624523437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105702147647374458166031249 79276610735530843624523437)
  ·
    refine ⟨29728729025824066359196289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79276610735530843624523437 29728729025824066359196289)
    ·
      refine ⟨22296546769368049769397217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29728729025824066359196289 22296546769368049769397217)
      ·
        refine ⟨16722410077026037327047913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22296546769368049769397217 16722410077026037327047913)
        ·
          refine ⟨12541807557769527995285935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16722410077026037327047913 12541807557769527995285935)
          ·
            refine ⟨18812711336654291992928903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12541807557769527995285935 18812711336654291992928903)
            ·
              refine ⟨28219067004981437989393355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18812711336654291992928903 28219067004981437989393355)
              ·
                refine ⟨42328600507472156984090033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28219067004981437989393355 42328600507472156984090033)
                ·
                  refine ⟨31746450380604117738067525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42328600507472156984090033 31746450380604117738067525)
                  ·
                    refine ⟨5952459446363272075887661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31746450380604117738067525 5952459446363272075887661)
                    ·
                      refine ⟨2232172292386227028457873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952459446363272075887661 2232172292386227028457873)
                      ·
                        rfl

theorem cell23_4347140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_4347140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347140 prefixEnd_4347140 := by exact prefixLift 4347140
  have htrace : WordTrace (prefixWord ++ tailWord_4347140) baseStart_4347140 baseEnd_4347140 := by
    simpa [prefixWord, tailWord_4347140, baseEnd_4347140] using wordTrace_append hprefix tailTrace_4347140
  have hstable : (prefixWord ++ tailWord_4347140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347140).length < 2 ^ (prefixWord ++ tailWord_4347140).sum := by decide
  have hdescent : baseEnd_4347140 < baseStart_4347140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347150 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4347150 : Nat := 118140960795 + 4347150 * 2 ^ 59
def prefixEnd_4347150 : Nat := 4983230072969 + 3 ^ 40 * 4347150 * 2
def baseEnd_4347150 : Nat := 2232177427192771989332827

theorem tailTrace_4347150 : CollatzResearch.WordTrace tailWord_4347150 prefixEnd_4347150 2232177427192771989332827 := by
  unfold tailWord_4347150
  simp only [CollatzResearch.WordTrace]
  refine ⟨19819198275128182369613863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105702390800683639304607269 19819198275128182369613863)
  ·
    refine ⟨29728797412692273554420795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19819198275128182369613863 29728797412692273554420795)
    ·
      refine ⟨44593196119038410331631193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29728797412692273554420795 44593196119038410331631193)
      ·
        refine ⟨33444897089278807748723395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44593196119038410331631193 33444897089278807748723395)
        ·
          refine ⟨50167345633918211623085093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33444897089278807748723395 50167345633918211623085093)
          ·
            refine ⟨9406377306359664679328455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50167345633918211623085093 9406377306359664679328455)
            ·
              refine ⟨14109565959539497018992683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9406377306359664679328455 14109565959539497018992683)
              ·
                refine ⟨21164348939309245528489025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14109565959539497018992683 21164348939309245528489025)
                ·
                  refine ⟨15873261704481934146366769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21164348939309245528489025 15873261704481934146366769)
                  ·
                    refine ⟨11904946278361450609775077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15873261704481934146366769 11904946278361450609775077)
                    ·
                      refine ⟨2232177427192771989332827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11904946278361450609775077 2232177427192771989332827)
                      ·
                        rfl

theorem cell23_4347150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4347150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347150 prefixEnd_4347150 := by exact prefixLift 4347150
  have htrace : WordTrace (prefixWord ++ tailWord_4347150) baseStart_4347150 baseEnd_4347150 := by
    simpa [prefixWord, tailWord_4347150, baseEnd_4347150] using wordTrace_append hprefix tailTrace_4347150
  have hstable : (prefixWord ++ tailWord_4347150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347150).length < 2 ^ (prefixWord ++ tailWord_4347150).sum := by decide
  have hdescent : baseEnd_4347150 < baseStart_4347150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347250 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_4347250 : Nat := 118140960795 + 4347250 * 2 ^ 59
def prefixEnd_4347250 : Nat := 4983230072969 + 3 ^ 40 * 4347250 * 2
def baseEnd_4347250 : Nat := 248025419473135733120263

theorem tailTrace_4347250 : CollatzResearch.WordTrace tailWord_4347250 prefixEnd_4347250 248025419473135733120263 := by
  unfold tailWord_4347250
  simp only [CollatzResearch.WordTrace]
  refine ⟨39639308375165794008887801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105704822333775450690367469 39639308375165794008887801)
  ·
    refine ⟨29729481281374345506665851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39639308375165794008887801 29729481281374345506665851)
    ·
      refine ⟨44594221922061518259998777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29729481281374345506665851 44594221922061518259998777)
      ·
        refine ⟨33445666441546138694999083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44594221922061518259998777 33445666441546138694999083)
        ·
          refine ⟨50168499662319208042498625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33445666441546138694999083 50168499662319208042498625)
          ·
            refine ⟨37626374746739406031873969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50168499662319208042498625 37626374746739406031873969)
            ·
              refine ⟨28219781060054554523905477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37626374746739406031873969 28219781060054554523905477)
              ·
                refine ⟨5291208948760228973232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28219781060054554523905477 5291208948760228973232277)
                ·
                  refine ⟨248025419473135733120263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5291208948760228973232277 248025419473135733120263)
                  ·
                    rfl

theorem cell23_4347250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_4347250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347250 prefixEnd_4347250 := by exact prefixLift 4347250
  have htrace : WordTrace (prefixWord ++ tailWord_4347250) baseStart_4347250 baseEnd_4347250 := by
    simpa [prefixWord, tailWord_4347250, baseEnd_4347250] using wordTrace_append hprefix tailTrace_4347250
  have hstable : (prefixWord ++ tailWord_4347250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347250).length < 2 ^ (prefixWord ++ tailWord_4347250).sum := by decide
  have hdescent : baseEnd_4347250 < baseStart_4347250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347267 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 6]
def baseStart_4347267 : Nat := 118140960795 + 4347267 * 2 ^ 59
def prefixEnd_4347267 : Nat := 4983230072969 + 3 ^ 40 * 4347267 * 2
def baseEnd_4347267 : Nat := 248026389381038670174421

theorem tailTrace_4347267 : CollatzResearch.WordTrace tailWord_4347267 prefixEnd_4347267 248026389381038670174421 := by
  unfold tailWord_4347267
  simp only [CollatzResearch.WordTrace]
  refine ⟨158557853541601587938920055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105705235694401058625946703 158557853541601587938920055)
  ·
    refine ⟨237836780312402381908380083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158557853541601587938920055 237836780312402381908380083)
    ·
      refine ⟨356755170468603572862570125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237836780312402381908380083 356755170468603572862570125)
      ·
        refine ⟨133783188925726339823463797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356755170468603572862570125 133783188925726339823463797)
        ·
          refine ⟨12542173961786844358449731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133783188925726339823463797 12542173961786844358449731)
          ·
            refine ⟨18813260942680266537674597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12542173961786844358449731 18813260942680266537674597)
            ·
              refine ⟨3527486426752549975813987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18813260942680266537674597 3527486426752549975813987)
              ·
                refine ⟨5291229640128824963720981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527486426752549975813987 5291229640128824963720981)
                ·
                  refine ⟨248026389381038670174421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5291229640128824963720981 248026389381038670174421)
                  ·
                    rfl

theorem cell23_4347267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 6].length) (baseStart_4347267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347267 prefixEnd_4347267 := by exact prefixLift 4347267
  have htrace : WordTrace (prefixWord ++ tailWord_4347267) baseStart_4347267 baseEnd_4347267 := by
    simpa [prefixWord, tailWord_4347267, baseEnd_4347267] using wordTrace_append hprefix tailTrace_4347267
  have hstable : (prefixWord ++ tailWord_4347267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347267).length < 2 ^ (prefixWord ++ tailWord_4347267).sum := by decide
  have hdescent : baseEnd_4347267 < baseStart_4347267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347317 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4347317 : Nat := 118140960795 + 4347317 * 2 ^ 59
def prefixEnd_4347317 : Nat := 4983230072969 + 3 ^ 40 * 4347317 * 2
def baseEnd_4347317 : Nat := 2232263178462072835944559

theorem tailTrace_4347317 : CollatzResearch.WordTrace tailWord_4347317 prefixEnd_4347317 2232263178462072835944559 := by
  unfold tailWord_4347317
  simp only [CollatzResearch.WordTrace]
  refine ⟨158559677191420446478240205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105706451460946964318826803 158559677191420446478240205)
  ·
    refine ⟨59459878946782667429340077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158559677191420446478240205 59459878946782667429340077)
    ·
      refine ⟨22297454605043500286002529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59459878946782667429340077 22297454605043500286002529)
      ·
        refine ⟨16723090953782625214501897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22297454605043500286002529 16723090953782625214501897)
        ·
          refine ⟨12542318215336968910876423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16723090953782625214501897 12542318215336968910876423)
          ·
            refine ⟨18813477323005453366314635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12542318215336968910876423 18813477323005453366314635)
            ·
              refine ⟨28220215984508180049471953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18813477323005453366314635 28220215984508180049471953)
              ·
                refine ⟨21165161988381135037103965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28220215984508180049471953 21165161988381135037103965)
                ·
                  refine ⟨7936935745642925638913987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21165161988381135037103965 7936935745642925638913987)
                  ·
                    refine ⟨11905403618464388458370981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7936935745642925638913987 11905403618464388458370981)
                    ·
                      refine ⟨2232263178462072835944559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11905403618464388458370981 2232263178462072835944559)
                      ·
                        rfl

theorem cell23_4347317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4347317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347317 prefixEnd_4347317 := by exact prefixLift 4347317
  have htrace : WordTrace (prefixWord ++ tailWord_4347317) baseStart_4347317 baseEnd_4347317 := by
    simpa [prefixWord, tailWord_4347317, baseEnd_4347317] using wordTrace_append hprefix tailTrace_4347317
  have hstable : (prefixWord ++ tailWord_4347317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347317).length < 2 ^ (prefixWord ++ tailWord_4347317).sum := by decide
  have hdescent : baseEnd_4347317 < baseStart_4347317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347320 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_4347320 : Nat := 118140960795 + 4347320 * 2 ^ 59
def prefixEnd_4347320 : Nat := 4983230072969 + 3 ^ 40 * 4347320 * 2
def baseEnd_4347320 : Nat := 2232264718904036324207045

theorem tailTrace_4347320 : CollatzResearch.WordTrace tailWord_4347320 prefixEnd_4347320 2232264718904036324207045 := by
  unfold tailWord_4347320
  simp only [CollatzResearch.WordTrace]
  refine ⟨79279893305204788995299707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105706524406939718660399609 79279893305204788995299707)
  ·
    refine ⟨118919839957807183492949561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79279893305204788995299707 118919839957807183492949561)
    ·
      refine ⟨89189879968355387619712171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118919839957807183492949561 89189879968355387619712171)
      ·
        refine ⟨133784819952533081429568257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89189879968355387619712171 133784819952533081429568257)
        ·
          refine ⟨100338614964399811072176193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133784819952533081429568257 100338614964399811072176193)
          ·
            refine ⟨75253961223299858304132145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100338614964399811072176193 75253961223299858304132145)
            ·
              refine ⟨56440470917474893728099109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75253961223299858304132145 56440470917474893728099109)
              ·
                refine ⟨10582588297026542574018583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56440470917474893728099109 10582588297026542574018583)
                ·
                  refine ⟨15873882445539813861027875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10582588297026542574018583 15873882445539813861027875)
                  ·
                    refine ⟨23810823668309720791541813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15873882445539813861027875 23810823668309720791541813)
                    ·
                      refine ⟨2232264718904036324207045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23810823668309720791541813 2232264718904036324207045)
                      ·
                        rfl

theorem cell23_4347320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_4347320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347320 prefixEnd_4347320 := by exact prefixLift 4347320
  have htrace : WordTrace (prefixWord ++ tailWord_4347320) baseStart_4347320 baseEnd_4347320 := by
    simpa [prefixWord, tailWord_4347320, baseEnd_4347320] using wordTrace_append hprefix tailTrace_4347320
  have hstable : (prefixWord ++ tailWord_4347320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347320).length < 2 ^ (prefixWord ++ tailWord_4347320).sum := by decide
  have hdescent : baseEnd_4347320 < baseStart_4347320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347337 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 3]
def baseStart_4347337 : Nat := 118140960795 + 4347337 * 2 ^ 59
def prefixEnd_4347337 : Nat := 4983230072969 + 3 ^ 40 * 4347337 * 2
def baseEnd_4347337 : Nat := 2232273448075162757694467

theorem tailTrace_4347337 : CollatzResearch.WordTrace tailWord_4347337 prefixEnd_4347337 2232273448075162757694467 := by
  unfold tailWord_4347337
  simp only [CollatzResearch.WordTrace]
  refine ⟨158560406651347989893968265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105706937767565326595978843 158560406651347989893968265)
  ·
    refine ⟨118920304988510992420476199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158560406651347989893968265 118920304988510992420476199)
    ·
      refine ⟨178380457482766488630714299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118920304988510992420476199 178380457482766488630714299)
      ·
        refine ⟨267570686224149732946071449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178380457482766488630714299 267570686224149732946071449)
        ·
          refine ⟨200678014668112299709553587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267570686224149732946071449 200678014668112299709553587)
          ·
            refine ⟨301017022002168449564330381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200678014668112299709553587 301017022002168449564330381)
            ·
              refine ⟨112881383250813168586623893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301017022002168449564330381 112881383250813168586623893)
              ·
                refine ⟨5291314839881867277497995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112881383250813168586623893 5291314839881867277497995)
                ·
                  refine ⟨7936972259822800916246993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291314839881867277497995 7936972259822800916246993)
                  ·
                    refine ⟨5952729194867100687185245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7936972259822800916246993 5952729194867100687185245)
                    ·
                      refine ⟨2232273448075162757694467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952729194867100687185245 2232273448075162757694467)
                      ·
                        rfl

theorem cell23_4347337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_4347337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347337 prefixEnd_4347337 := by exact prefixLift 4347337
  have htrace : WordTrace (prefixWord ++ tailWord_4347337) baseStart_4347337 baseEnd_4347337 := by
    simpa [prefixWord, tailWord_4347337, baseEnd_4347337] using wordTrace_append hprefix tailTrace_4347337
  have hstable : (prefixWord ++ tailWord_4347337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347337).length < 2 ^ (prefixWord ++ tailWord_4347337).sum := by decide
  have hdescent : baseEnd_4347337 < baseStart_4347337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347348 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_4347348 : Nat := 118140960795 + 4347348 * 2 ^ 59
def prefixEnd_4347348 : Nat := 4983230072969 + 3 ^ 40 * 4347348 * 2
def baseEnd_4347348 : Nat := 744093032120787404885639

theorem tailTrace_4347348 : CollatzResearch.WordTrace tailWord_4347348 prefixEnd_4347348 744093032120787404885639 := by
  unfold tailWord_4347348
  simp only [CollatzResearch.WordTrace]
  refine ⟨79280403927154069386309349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105707205236205425848412465 79280403927154069386309349)
  ·
    refine ⟨14865075736341388009933003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79280403927154069386309349 14865075736341388009933003)
    ·
      refine ⟨22297613604512082014899505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14865075736341388009933003 22297613604512082014899505)
      ·
        refine ⟨16723210203384061511174629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22297613604512082014899505 16723210203384061511174629)
        ·
          refine ⟨3135601913134511533345243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16723210203384061511174629 3135601913134511533345243)
          ·
            refine ⟨4703402869701767300017865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135601913134511533345243 4703402869701767300017865)
            ·
              refine ⟨3527552152276325475013399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4703402869701767300017865 3527552152276325475013399)
              ·
                refine ⟨5291328228414488212520099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527552152276325475013399 5291328228414488212520099)
                ·
                  refine ⟨7936992342621732318780149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291328228414488212520099 7936992342621732318780149)
                  ·
                    refine ⟨744093032120787404885639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7936992342621732318780149 744093032120787404885639)
                    ·
                      rfl

theorem cell23_4347348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_4347348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347348 prefixEnd_4347348 := by exact prefixLift 4347348
  have htrace : WordTrace (prefixWord ++ tailWord_4347348) baseStart_4347348 baseEnd_4347348 := by
    simpa [prefixWord, tailWord_4347348, baseEnd_4347348] using wordTrace_append hprefix tailTrace_4347348
  have hstable : (prefixWord ++ tailWord_4347348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347348).length < 2 ^ (prefixWord ++ tailWord_4347348).sum := by decide
  have hdescent : baseEnd_4347348 < baseStart_4347348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347354 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_4347354 : Nat := 118140960795 + 4347354 * 2 ^ 59
def prefixEnd_4347354 : Nat := 4983230072969 + 3 ^ 40 * 4347354 * 2
def baseEnd_4347354 : Nat := 2232282177246289191181889

theorem tailTrace_4347354 : CollatzResearch.WordTrace tailWord_4347354 prefixEnd_4347354 2232282177246289191181889 := by
  unfold tailWord_4347354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39640256673071600449334279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105707351128190934531558077 39640256673071600449334279)
  ·
    refine ⟨59460385009607400674001419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39640256673071600449334279 59460385009607400674001419)
    ·
      refine ⟨89190577514411101011002129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59460385009607400674001419 89190577514411101011002129)
      ·
        refine ⟨66892933135808325758251597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89190577514411101011002129 66892933135808325758251597)
        ·
          refine ⟨25084849925928122159344349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66892933135808325758251597 25084849925928122159344349)
          ·
            refine ⟨9406818722223045809754131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25084849925928122159344349 9406818722223045809754131)
            ·
              refine ⟨14110228083334568714631197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9406818722223045809754131 14110228083334568714631197)
              ·
                refine ⟨5291335531250463267986699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14110228083334568714631197 5291335531250463267986699)
                ·
                  refine ⟨7937003296875694901980049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291335531250463267986699 7937003296875694901980049)
                  ·
                    refine ⟨5952752472656771176485037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7937003296875694901980049 5952752472656771176485037)
                    ·
                      refine ⟨2232282177246289191181889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952752472656771176485037 2232282177246289191181889)
                      ·
                        rfl

theorem cell23_4347354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_4347354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347354 prefixEnd_4347354 := by exact prefixLift 4347354
  have htrace : WordTrace (prefixWord ++ tailWord_4347354) baseStart_4347354 baseEnd_4347354 := by
    simpa [prefixWord, tailWord_4347354, baseEnd_4347354] using wordTrace_append hprefix tailTrace_4347354
  have hstable : (prefixWord ++ tailWord_4347354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347354).length < 2 ^ (prefixWord ++ tailWord_4347354).sum := by decide
  have hdescent : baseEnd_4347354 < baseStart_4347354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347381 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4347381 : Nat := 118140960795 + 4347381 * 2 ^ 59
def prefixEnd_4347381 : Nat := 4983230072969 + 3 ^ 40 * 4347381 * 2
def baseEnd_4347381 : Nat := 2232296041223960585544265

theorem tailTrace_4347381 : CollatzResearch.WordTrace tailWord_4347381 prefixEnd_4347381 2232296041223960585544265 := by
  unfold tailWord_4347381
  simp only [CollatzResearch.WordTrace]
  refine ⟨158562011463188585408569997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105708007642125723605713331 158562011463188585408569997)
  ·
    refine ⟨59460754298695719528213749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158562011463188585408569997 59460754298695719528213749)
    ·
      refine ⟨5574445715502723705770039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59460754298695719528213749 5574445715502723705770039)
      ·
        refine ⟨8361668573254085558655059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5574445715502723705770039 8361668573254085558655059)
        ·
          refine ⟨12542502859881128337982589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8361668573254085558655059 12542502859881128337982589)
          ·
            refine ⟨4703438572455423126743471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12542502859881128337982589 4703438572455423126743471)
            ·
              refine ⟨7055157858683134690115207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703438572455423126743471 7055157858683134690115207)
              ·
                refine ⟨10582736788024702035172811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7055157858683134690115207 10582736788024702035172811)
                ·
                  refine ⟨15874105182037053052759217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10582736788024702035172811 15874105182037053052759217)
                  ·
                    refine ⟨11905578886527789789569413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15874105182037053052759217 11905578886527789789569413)
                    ·
                      refine ⟨2232296041223960585544265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11905578886527789789569413 2232296041223960585544265)
                      ·
                        rfl

theorem cell23_4347381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4347381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347381 prefixEnd_4347381 := by exact prefixLift 4347381
  have htrace : WordTrace (prefixWord ++ tailWord_4347381) baseStart_4347381 baseEnd_4347381 := by
    simpa [prefixWord, tailWord_4347381, baseEnd_4347381] using wordTrace_append hprefix tailTrace_4347381
  have hstable : (prefixWord ++ tailWord_4347381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347381).length < 2 ^ (prefixWord ++ tailWord_4347381).sum := by decide
  have hdescent : baseEnd_4347381 < baseStart_4347381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347384 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_4347384 : Nat := 118140960795 + 4347384 * 2 ^ 59
def prefixEnd_4347384 : Nat := 4983230072969 + 3 ^ 40 * 4347384 * 2
def baseEnd_4347384 : Nat := 2232297581665924073806751

theorem tailTrace_4347384 : CollatzResearch.WordTrace tailWord_4347384 prefixEnd_4347384 2232297581665924073806751 := by
  unfold tailWord_4347384
  simp only [CollatzResearch.WordTrace]
  refine ⟨79281060441088858460464603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105708080588118477947286137 79281060441088858460464603)
  ·
    refine ⟨118921590661633287690696905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79281060441088858460464603 118921590661633287690696905)
    ·
      refine ⟨89191192996224965768022679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118921590661633287690696905 89191192996224965768022679)
      ·
        refine ⟨133786789494337448652034019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89191192996224965768022679 133786789494337448652034019)
        ·
          refine ⟨200680184241506172978051029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133786789494337448652034019 200680184241506172978051029)
          ·
            refine ⟨4703441818160300929173071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200680184241506172978051029 4703441818160300929173071)
            ·
              refine ⟨7055162727240451393759607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703441818160300929173071 7055162727240451393759607)
              ·
                refine ⟨10582744090860677090639411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7055162727240451393759607 10582744090860677090639411)
                ·
                  refine ⟨15874116136291015635959117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10582744090860677090639411 15874116136291015635959117)
                  ·
                    refine ⟨5952793551109130863484669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15874116136291015635959117 5952793551109130863484669)
                    ·
                      refine ⟨2232297581665924073806751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5952793551109130863484669 2232297581665924073806751)
                      ·
                        rfl

theorem cell23_4347384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_4347384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347384 prefixEnd_4347384 := by exact prefixLift 4347384
  have htrace : WordTrace (prefixWord ++ tailWord_4347384) baseStart_4347384 baseEnd_4347384 := by
    simpa [prefixWord, tailWord_4347384, baseEnd_4347384] using wordTrace_append hprefix tailTrace_4347384
  have hstable : (prefixWord ++ tailWord_4347384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347384).length < 2 ^ (prefixWord ++ tailWord_4347384).sum := by decide
  have hdescent : baseEnd_4347384 < baseStart_4347384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347400 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_4347400 : Nat := 118140960795 + 4347400 * 2 ^ 59
def prefixEnd_4347400 : Nat := 4983230072969 + 3 ^ 40 * 4347400 * 2
def baseEnd_4347400 : Nat := 744101932452132003735559

theorem tailTrace_4347400 : CollatzResearch.WordTrace tailWord_4347400 prefixEnd_4347400 744101932452132003735559 := by
  unfold tailWord_4347400
  simp only [CollatzResearch.WordTrace]
  refine ⟨79281352225059875826755827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105708469633413167769007769 79281352225059875826755827)
  ·
    refine ⟨118922028337589813740133741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79281352225059875826755827 118922028337589813740133741)
    ·
      refine ⟨44595760626596180152550153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118922028337589813740133741 44595760626596180152550153)
      ·
        refine ⟨33446820469947135114412615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44595760626596180152550153 33446820469947135114412615)
        ·
          refine ⟨50170230704920702671618923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33446820469947135114412615 50170230704920702671618923)
          ·
            refine ⟨75255346057381054007428385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50170230704920702671618923 75255346057381054007428385)
            ·
              refine ⟨56441509543035790505571289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75255346057381054007428385 56441509543035790505571289)
              ·
                refine ⟨42331132157276842879178467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56441509543035790505571289 42331132157276842879178467)
                ·
                  refine ⟨63496698235915264318767701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42331132157276842879178467 63496698235915264318767701)
                  ·
                    refine ⟨744101932452132003735559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63496698235915264318767701 744101932452132003735559)
                    ·
                      rfl

theorem cell23_4347400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_4347400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347400 prefixEnd_4347400 := by exact prefixLift 4347400
  have htrace : WordTrace (prefixWord ++ tailWord_4347400) baseStart_4347400 baseEnd_4347400 := by
    simpa [prefixWord, tailWord_4347400, baseEnd_4347400] using wordTrace_append hprefix tailTrace_4347400
  have hstable : (prefixWord ++ tailWord_4347400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347400).length < 2 ^ (prefixWord ++ tailWord_4347400).sum := by decide
  have hdescent : baseEnd_4347400 < baseStart_4347400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347462 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4347462 : Nat := 118140960795 + 4347462 * 2 ^ 59
def prefixEnd_4347462 : Nat := 4983230072969 + 3 ^ 40 * 4347462 * 2
def baseEnd_4347462 : Nat := 2232337633156974768631393

theorem tailTrace_4347462 : CollatzResearch.WordTrace tailWord_4347462 prefixEnd_4347462 2232337633156974768631393 := by
  unfold tailWord_4347462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4955155180496723007570895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105709977183930090828179093 4955155180496723007570895)
  ·
    refine ⟨7432732770745084511356343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4955155180496723007570895 7432732770745084511356343)
    ·
      refine ⟨11149099156117626767034515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7432732770745084511356343 11149099156117626767034515)
      ·
        refine ⟨16723648734176440150551773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11149099156117626767034515 16723648734176440150551773)
        ·
          refine ⟨6271368275316165056456915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16723648734176440150551773 6271368275316165056456915)
          ·
            refine ⟨9407052412974247584685373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6271368275316165056456915 9407052412974247584685373)
            ·
              refine ⟨3527644654865342844257015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9407052412974247584685373 3527644654865342844257015)
              ·
                refine ⟨5291466982298014266385523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527644654865342844257015 5291466982298014266385523)
                ·
                  refine ⟨7937200473447021399578285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291466982298014266385523 7937200473447021399578285)
                  ·
                    refine ⟨2976450177542633024841857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7937200473447021399578285 2976450177542633024841857)
                    ·
                      refine ⟨2232337633156974768631393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976450177542633024841857 2232337633156974768631393)
                      ·
                        rfl

theorem cell23_4347462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4347462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347462 prefixEnd_4347462 := by exact prefixLift 4347462
  have htrace : WordTrace (prefixWord ++ tailWord_4347462) baseStart_4347462 baseEnd_4347462 := by
    simpa [prefixWord, tailWord_4347462, baseEnd_4347462] using wordTrace_append hprefix tailTrace_4347462
  have hstable : (prefixWord ++ tailWord_4347462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347462).length < 2 ^ (prefixWord ++ tailWord_4347462).sum := by decide
  have hdescent : baseEnd_4347462 < baseStart_4347462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347497 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_4347497 : Nat := 118140960795 + 4347497 * 2 ^ 59
def prefixEnd_4347497 : Nat := 4983230072969 + 3 ^ 40 * 4347497 * 2
def baseEnd_4347497 : Nat := 2232355604979882131693731

theorem tailTrace_4347497 : CollatzResearch.WordTrace tailWord_4347497 prefixEnd_4347497 2232355604979882131693731 := by
  unfold tailWord_4347497
  simp only [CollatzResearch.WordTrace]
  refine ⟨158566242330768337219792745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105710828220512224813195163 158566242330768337219792745)
  ·
    refine ⟨118924681748076252914844559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158566242330768337219792745 118924681748076252914844559)
    ·
      refine ⟨178387022622114379372266839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118924681748076252914844559 178387022622114379372266839)
      ·
        refine ⟨267580533933171569058400259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178387022622114379372266839 267580533933171569058400259)
        ·
          refine ⟨401370800899757353587600389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267580533933171569058400259 401370800899757353587600389)
          ·
            refine ⟨75257025168704503797675073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 401370800899757353587600389 75257025168704503797675073)
            ·
              refine ⟨56442768876528377848256305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75257025168704503797675073 56442768876528377848256305)
              ·
                refine ⟨42332076657396283386192229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56442768876528377848256305 42332076657396283386192229)
                ·
                  refine ⟨7937264373261803134911043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42332076657396283386192229 7937264373261803134911043)
                  ·
                    refine ⟨11905896559892704702366565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7937264373261803134911043 11905896559892704702366565)
                    ·
                      refine ⟨2232355604979882131693731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11905896559892704702366565 2232355604979882131693731)
                      ·
                        rfl

theorem cell23_4347497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_4347497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347497 prefixEnd_4347497 := by exact prefixLift 4347497
  have htrace : WordTrace (prefixWord ++ tailWord_4347497) baseStart_4347497 baseEnd_4347497 := by
    simpa [prefixWord, tailWord_4347497, baseEnd_4347497] using wordTrace_append hprefix tailTrace_4347497
  have hstable : (prefixWord ++ tailWord_4347497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347497).length < 2 ^ (prefixWord ++ tailWord_4347497).sum := by decide
  have hdescent : baseEnd_4347497 < baseStart_4347497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347527 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4347527 : Nat := 118140960795 + 4347527 * 2 ^ 59
def prefixEnd_4347527 : Nat := 4983230072969 + 3 ^ 40 * 4347527 * 2
def baseEnd_4347527 : Nat := 2232371009399517014318593

theorem tailTrace_4347527 : CollatzResearch.WordTrace tailWord_4347527 prefixEnd_4347527 2232371009399517014318593 := by
  unfold tailWord_4347527
  simp only [CollatzResearch.WordTrace]
  refine ⟨158567336520659652343384835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105711557680439768228923223 158567336520659652343384835)
  ·
    refine ⟨237851004780989478515077253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158567336520659652343384835 237851004780989478515077253)
    ·
      refine ⟨44597063396435527221576985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237851004780989478515077253 44597063396435527221576985)
      ·
        refine ⟨33447797547326645416182739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44597063396435527221576985 33447797547326645416182739)
        ·
          refine ⟨50171696320989968124274109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33447797547326645416182739 50171696320989968124274109)
          ·
            refine ⟨18814386120371238046602791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50171696320989968124274109 18814386120371238046602791)
            ·
              refine ⟨28221579180556857069904187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18814386120371238046602791 28221579180556857069904187)
              ·
                refine ⟨42332368770835285604856281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28221579180556857069904187 42332368770835285604856281)
                ·
                  refine ⟨31749276578126464203642211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42332368770835285604856281 31749276578126464203642211)
                  ·
                    refine ⟨47623914867189696305463317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31749276578126464203642211 47623914867189696305463317)
                    ·
                      refine ⟨2232371009399517014318593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47623914867189696305463317 2232371009399517014318593)
                      ·
                        rfl

theorem cell23_4347527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4347527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347527 prefixEnd_4347527 := by exact prefixLift 4347527
  have htrace : WordTrace (prefixWord ++ tailWord_4347527) baseStart_4347527 baseEnd_4347527 := by
    simpa [prefixWord, tailWord_4347527, baseEnd_4347527] using wordTrace_append hprefix tailTrace_4347527
  have hstable : (prefixWord ++ tailWord_4347527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347527).length < 2 ^ (prefixWord ++ tailWord_4347527).sum := by decide
  have hdescent : baseEnd_4347527 < baseStart_4347527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347537 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 6]
def baseStart_4347537 : Nat := 118140960795 + 4347537 * 2 ^ 59
def prefixEnd_4347537 : Nat := 4983230072969 + 3 ^ 40 * 4347537 * 2
def baseEnd_4347537 : Nat := 248041793800673552799283

theorem tailTrace_4347537 : CollatzResearch.WordTrace tailWord_4347537 prefixEnd_4347537 248041793800673552799283 := by
  unfold tailWord_4347537
  simp only [CollatzResearch.WordTrace]
  refine ⟨158567701250623424051248865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105711800833748949367499243 158567701250623424051248865)
  ·
    refine ⟨118925775937967568038436649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158567701250623424051248865 118925775937967568038436649)
    ·
      refine ⟨89194331953475676028827487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118925775937967568038436649 89194331953475676028827487)
      ·
        refine ⟨133791497930213514043241231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89194331953475676028827487 133791497930213514043241231)
        ·
          refine ⟨200687246895320271064861847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133791497930213514043241231 200687246895320271064861847)
          ·
            refine ⟨301030870342980406597292771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200687246895320271064861847 301030870342980406597292771)
            ·
              refine ⟨451546305514470609895939157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301030870342980406597292771 451546305514470609895939157)
              ·
                refine ⟨5291558267747702459718037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 451546305514470609895939157 5291558267747702459718037)
                ·
                  refine ⟨248041793800673552799283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5291558267747702459718037 248041793800673552799283)
                  ·
                    rfl

theorem cell23_4347537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 6].length) (baseStart_4347537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347537 prefixEnd_4347537 := by exact prefixLift 4347537
  have htrace : WordTrace (prefixWord ++ tailWord_4347537) baseStart_4347537 baseEnd_4347537 := by
    simpa [prefixWord, tailWord_4347537, baseEnd_4347537] using wordTrace_append hprefix tailTrace_4347537
  have hstable : (prefixWord ++ tailWord_4347537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347537).length < 2 ^ (prefixWord ++ tailWord_4347537).sum := by decide
  have hdescent : baseEnd_4347537 < baseStart_4347537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347584 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 1, 5]
def baseStart_4347584 : Nat := 118140960795 + 4347584 * 2 ^ 59
def prefixEnd_4347584 : Nat := 4983230072969 + 3 ^ 40 * 4347584 * 2
def baseEnd_4347584 : Nat := 744133425932274430435277

theorem tailTrace_4347584 : CollatzResearch.WordTrace tailWord_4347584 prefixEnd_4347584 744133425932274430435277 := by
  unfold tailWord_4347584
  simp only [CollatzResearch.WordTrace]
  refine ⟨79284707740726575539104903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105712943654302100718806537 79284707740726575539104903)
  ·
    refine ⟨118927061611089863308657355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79284707740726575539104903 118927061611089863308657355)
    ·
      refine ⟨178390592416634794962986033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118927061611089863308657355 178390592416634794962986033)
      ·
        refine ⟨133792944312476096222239525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178390592416634794962986033 133792944312476096222239525)
        ·
          refine ⟨25086177058589268041669911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133792944312476096222239525 25086177058589268041669911)
          ·
            refine ⟨37629265587883902062504867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25086177058589268041669911 37629265587883902062504867)
            ·
              refine ⟨56443898381825853093757301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37629265587883902062504867 56443898381825853093757301)
              ·
                refine ⟨5291615473296173727539747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56443898381825853093757301 5291615473296173727539747)
                ·
                  refine ⟨7937423209944260591309621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291615473296173727539747 7937423209944260591309621)
                  ·
                    refine ⟨744133425932274430435277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7937423209944260591309621 744133425932274430435277)
                    ·
                      rfl

theorem cell23_4347584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_4347584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347584 prefixEnd_4347584 := by exact prefixLift 4347584
  have htrace : WordTrace (prefixWord ++ tailWord_4347584) baseStart_4347584 baseEnd_4347584 := by
    simpa [prefixWord, tailWord_4347584, baseEnd_4347584] using wordTrace_append hprefix tailTrace_4347584
  have hstable : (prefixWord ++ tailWord_4347584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347584).length < 2 ^ (prefixWord ++ tailWord_4347584).sum := by decide
  have hdescent : baseEnd_4347584 < baseStart_4347584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347591 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_4347591 : Nat := 118140960795 + 4347591 * 2 ^ 59
def prefixEnd_4347591 : Nat := 4983230072969 + 3 ^ 40 * 4347591 * 2
def baseEnd_4347591 : Nat := 2232403872161404763918299

theorem tailTrace_4347591 : CollatzResearch.WordTrace tailWord_4347591 prefixEnd_4347591 2232403872161404763918299 := by
  unfold tailWord_4347591
  simp only [CollatzResearch.WordTrace]
  refine ⟨158569670792427791273714627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105713113861618527515809751 158569670792427791273714627)
  ·
    refine ⟨237854506188641686910571941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158569670792427791273714627 237854506188641686910571941)
    ·
      refine ⟨44597719910370316295732239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237854506188641686910571941 44597719910370316295732239)
      ·
        refine ⟨66896579865555474443598359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44597719910370316295732239 66896579865555474443598359)
        ·
          refine ⟨100344869798333211665397539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66896579865555474443598359 100344869798333211665397539)
          ·
            refine ⟨150517304697499817498096309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100344869798333211665397539 150517304697499817498096309)
            ·
              refine ⟨14110997315390607890446529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150517304697499817498096309 14110997315390607890446529)
              ·
                refine ⟨10583247986542955917834897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14110997315390607890446529 10583247986542955917834897)
                ·
                  refine ⟨7937435989907216938376173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10583247986542955917834897 7937435989907216938376173)
                  ·
                    refine ⟨2976538496215206351891065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7937435989907216938376173 2976538496215206351891065)
                    ·
                      refine ⟨2232403872161404763918299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976538496215206351891065 2232403872161404763918299)
                      ·
                        rfl

theorem cell23_4347591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_4347591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347591 prefixEnd_4347591 := by exact prefixLift 4347591
  have htrace : WordTrace (prefixWord ++ tailWord_4347591) baseStart_4347591 baseEnd_4347591 := by
    simpa [prefixWord, tailWord_4347591, baseEnd_4347591] using wordTrace_append hprefix tailTrace_4347591
  have hstable : (prefixWord ++ tailWord_4347591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347591).length < 2 ^ (prefixWord ++ tailWord_4347591).sum := by decide
  have hdescent : baseEnd_4347591 < baseStart_4347591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347627 : List Nat := [1, 1, 1, 1, 2, 4, 4, 9]
def baseStart_4347627 : Nat := 118140960795 + 4347627 * 2 ^ 59
def prefixEnd_4347627 : Nat := 4983230072969 + 3 ^ 40 * 4347627 * 2
def baseEnd_4347627 : Nat := 82682309535739504558079

theorem tailTrace_4347627 : CollatzResearch.WordTrace tailWord_4347627 prefixEnd_4347627 82682309535739504558079 := by
  unfold tailWord_4347627
  simp only [CollatzResearch.WordTrace]
  refine ⟨158570983820297369422025135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105713989213531579614683423 158570983820297369422025135)
  ·
    refine ⟨237856475730446054133037703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158570983820297369422025135 237856475730446054133037703)
    ·
      refine ⟨356784713595669081199556555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237856475730446054133037703 356784713595669081199556555)
      ·
        refine ⟨535177070393503621799334833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356784713595669081199556555 535177070393503621799334833)
        ·
          refine ⟨401382802795127716349501125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535177070393503621799334833 401382802795127716349501125)
          ·
            refine ⟨75259275524086446815531461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 401382802795127716349501125 75259275524086446815531461)
            ·
              refine ⟨14111114160766208777912149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75259275524086446815531461 14111114160766208777912149)
              ·
                refine ⟨82682309535739504558079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14111114160766208777912149 82682309535739504558079)
                ·
                  rfl

theorem cell23_4347627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 9].length) (baseStart_4347627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347627 prefixEnd_4347627 := by exact prefixLift 4347627
  have htrace : WordTrace (prefixWord ++ tailWord_4347627) baseStart_4347627 baseEnd_4347627 := by
    simpa [prefixWord, tailWord_4347627, baseEnd_4347627] using wordTrace_append hprefix tailTrace_4347627
  have hstable : (prefixWord ++ tailWord_4347627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347627).length < 2 ^ (prefixWord ++ tailWord_4347627).sum := by decide
  have hdescent : baseEnd_4347627 < baseStart_4347627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347671 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4347671 : Nat := 118140960795 + 4347671 * 2 ^ 59
def prefixEnd_4347671 : Nat := 4983230072969 + 3 ^ 40 * 4347671 * 2
def baseEnd_4347671 : Nat := 2232444950613764450917931

theorem tailTrace_4347671 : CollatzResearch.WordTrace tailWord_4347671 prefixEnd_4347671 2232444950613764450917931 := by
  unfold tailWord_4347671
  simp only [CollatzResearch.WordTrace]
  refine ⟨158572588632137964936626867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105715059088091976624417911 158572588632137964936626867)
  ·
    refine ⟨237858882948206947404940301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158572588632137964936626867 237858882948206947404940301)
    ·
      refine ⟨89197081105577605276852613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237858882948206947404940301 89197081105577605276852613)
      ·
        refine ⟨16724452707295800989409865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89197081105577605276852613 16724452707295800989409865)
        ·
          refine ⟨12543339530471850742057399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16724452707295800989409865 12543339530471850742057399)
          ·
            refine ⟨18815009295707776113086099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12543339530471850742057399 18815009295707776113086099)
            ·
              refine ⟨28222513943561664169629149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18815009295707776113086099 28222513943561664169629149)
              ·
                refine ⟨10583442728835624063610931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28222513943561664169629149 10583442728835624063610931)
                ·
                  refine ⟨15875164093253436095416397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10583442728835624063610931 15875164093253436095416397)
                  ·
                    refine ⟨5953186534970038535781149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15875164093253436095416397 5953186534970038535781149)
                    ·
                      refine ⟨2232444950613764450917931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5953186534970038535781149 2232444950613764450917931)
                      ·
                        rfl

theorem cell23_4347671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4347671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347671 prefixEnd_4347671 := by exact prefixLift 4347671
  have htrace : WordTrace (prefixWord ++ tailWord_4347671) baseStart_4347671 baseEnd_4347671 := by
    simpa [prefixWord, tailWord_4347671, baseEnd_4347671] using wordTrace_append hprefix tailTrace_4347671
  have hstable : (prefixWord ++ tailWord_4347671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347671).length < 2 ^ (prefixWord ++ tailWord_4347671).sum := by decide
  have hdescent : baseEnd_4347671 < baseStart_4347671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347704 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_4347704 : Nat := 118140960795 + 4347704 * 2 ^ 59
def prefixEnd_4347704 : Nat := 4983230072969 + 3 ^ 40 * 4347704 * 2
def baseEnd_4347704 : Nat := 744153965158454273935093

theorem tailTrace_4347704 : CollatzResearch.WordTrace tailWord_4347704 prefixEnd_4347704 744153965158454273935093 := by
  unfold tailWord_4347704
  simp only [CollatzResearch.WordTrace]
  refine ⟨79286896120509205786289083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105715861494012274381718777 79286896120509205786289083)
  ·
    refine ⟨118930344180763808679433625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79286896120509205786289083 118930344180763808679433625)
    ·
      refine ⟨89197758135572856509575219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118930344180763808679433625 89197758135572856509575219)
      ·
        refine ⟨133796637203359284764362829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89197758135572856509575219 133796637203359284764362829)
        ·
          refine ⟨50173738951259731786636061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133796637203359284764362829 50173738951259731786636061)
          ·
            refine ⟨18815152106722399419988523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50173738951259731786636061 18815152106722399419988523)
            ·
              refine ⟨28222728160083599129982785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18815152106722399419988523 28222728160083599129982785)
              ·
                refine ⟨21167046120062699347487089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28222728160083599129982785 21167046120062699347487089)
                ·
                  refine ⟨15875284590047024510615317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21167046120062699347487089 15875284590047024510615317)
                  ·
                    refine ⟨744153965158454273935093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15875284590047024510615317 744153965158454273935093)
                    ·
                      rfl

theorem cell23_4347704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_4347704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347704 prefixEnd_4347704 := by exact prefixLift 4347704
  have htrace : WordTrace (prefixWord ++ tailWord_4347704) baseStart_4347704 baseEnd_4347704 := by
    simpa [prefixWord, tailWord_4347704, baseEnd_4347704] using wordTrace_append hprefix tailTrace_4347704
  have hstable : (prefixWord ++ tailWord_4347704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347704).length < 2 ^ (prefixWord ++ tailWord_4347704).sum := by decide
  have hdescent : baseEnd_4347704 < baseStart_4347704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347705 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4347705 : Nat := 118140960795 + 4347705 * 2 ^ 59
def prefixEnd_4347705 : Nat := 4983230072969 + 3 ^ 40 * 4347705 * 2
def baseEnd_4347705 : Nat := 2232462408956017317892775

theorem tailTrace_4347705 : CollatzResearch.WordTrace tailWord_4347705 prefixEnd_4347705 2232462408956017317892775 := by
  unfold tailWord_4347705
  simp only [CollatzResearch.WordTrace]
  refine ⟨158573828714014788743364569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105715885809343192495576379 158573828714014788743364569)
  ·
    refine ⟨118930371535511091557523427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158573828714014788743364569 118930371535511091557523427)
    ·
      refine ⟨178395557303266637336285141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118930371535511091557523427 178395557303266637336285141)
      ·
        refine ⟨4181145874295311812569183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 178395557303266637336285141 4181145874295311812569183)
        ·
          refine ⟨6271718811442967718853775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181145874295311812569183 6271718811442967718853775)
          ·
            refine ⟨9407578217164451578280663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6271718811442967718853775 9407578217164451578280663)
            ·
              refine ⟨14111367325746677367420995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9407578217164451578280663 14111367325746677367420995)
              ·
                refine ⟨21167050988620016051131493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14111367325746677367420995 21167050988620016051131493)
                ·
                  refine ⟨3968822060366253009587155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21167050988620016051131493 3968822060366253009587155)
                  ·
                    refine ⟨5953233090549379514380733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3968822060366253009587155 5953233090549379514380733)
                    ·
                      refine ⟨2232462408956017317892775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5953233090549379514380733 2232462408956017317892775)
                      ·
                        rfl

theorem cell23_4347705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4347705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347705 prefixEnd_4347705 := by exact prefixLift 4347705
  have htrace : WordTrace (prefixWord ++ tailWord_4347705) baseStart_4347705 baseEnd_4347705 := by
    simpa [prefixWord, tailWord_4347705, baseEnd_4347705] using wordTrace_append hprefix tailTrace_4347705
  have hstable : (prefixWord ++ tailWord_4347705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347705).length < 2 ^ (prefixWord ++ tailWord_4347705).sum := by decide
  have hdescent : baseEnd_4347705 < baseStart_4347705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347771 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 2, 5, 2]
def baseStart_4347771 : Nat := 118140960795 + 4347771 * 2 ^ 59
def prefixEnd_4347771 : Nat := 4983230072969 + 3 ^ 40 * 4347771 * 2
def baseEnd_4347771 : Nat := 2232496298679214059667471

theorem tailTrace_4347771 : CollatzResearch.WordTrace tailWord_4347771 prefixEnd_4347771 2232496298679214059667471 := by
  unfold tailWord_4347771
  simp only [CollatzResearch.WordTrace]
  refine ⟨158576235931775682015267167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105717490621183788010178111 158576235931775682015267167)
  ·
    refine ⟨237864353897663523022900751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158576235931775682015267167 237864353897663523022900751)
    ·
      refine ⟨356796530846495284534351127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237864353897663523022900751 356796530846495284534351127)
      ·
        refine ⟨535194796269742926801526691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356796530846495284534351127 535194796269742926801526691)
        ·
          refine ⟨802792194404614390202290037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535194796269742926801526691 802792194404614390202290037)
          ·
            refine ⟨75261768225432599081464691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 802792194404614390202290037 75261768225432599081464691)
            ·
              refine ⟨112892652338148898622197037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75261768225432599081464691 112892652338148898622197037)
              ·
                refine ⟨42334744626805836983323889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112892652338148898622197037 42334744626805836983323889)
                ·
                  refine ⟨31751058470104377737492917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42334744626805836983323889 31751058470104377737492917)
                  ·
                    refine ⟨2976661731572285412889961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31751058470104377737492917 2976661731572285412889961)
                    ·
                      refine ⟨2232496298679214059667471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976661731572285412889961 2232496298679214059667471)
                      ·
                        rfl

theorem cell23_4347771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5, 2].length) (baseStart_4347771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347771 prefixEnd_4347771 := by exact prefixLift 4347771
  have htrace : WordTrace (prefixWord ++ tailWord_4347771) baseStart_4347771 baseEnd_4347771 := by
    simpa [prefixWord, tailWord_4347771, baseEnd_4347771] using wordTrace_append hprefix tailTrace_4347771
  have hstable : (prefixWord ++ tailWord_4347771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347771).length < 2 ^ (prefixWord ++ tailWord_4347771).sum := by decide
  have hdescent : baseEnd_4347771 < baseStart_4347771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347801 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_4347801 : Nat := 118140960795 + 4347801 * 2 ^ 59
def prefixEnd_4347801 : Nat := 4983230072969 + 3 ^ 40 * 4347801 * 2
def baseEnd_4347801 : Nat := 2232511703098848942292333

theorem tailTrace_4347801 : CollatzResearch.WordTrace tailWord_4347801 prefixEnd_4347801 2232511703098848942292333 := by
  unfold tailWord_4347801
  simp only [CollatzResearch.WordTrace]
  refine ⟨158577330121666997138859257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105718220081111331425906171 158577330121666997138859257)
  ·
    refine ⟨118932997591250247854144443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158577330121666997138859257 118932997591250247854144443)
    ·
      refine ⟨178399496386875371781216665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118932997591250247854144443 178399496386875371781216665)
      ·
        refine ⟨133799622290156528835912499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178399496386875371781216665 133799622290156528835912499)
        ·
          refine ⟨200699433435234793253868749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133799622290156528835912499 200699433435234793253868749)
          ·
            refine ⟨75262287538213047470200781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200699433435234793253868749 75262287538213047470200781)
            ·
              refine ⟨28223357826829892801325293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75262287538213047470200781 28223357826829892801325293)
              ·
                refine ⟨10583759185061209800496985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28223357826829892801325293 10583759185061209800496985)
                ·
                  refine ⟨7937819388795907350372739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10583759185061209800496985 7937819388795907350372739)
                  ·
                    refine ⟨11906729083193861025559109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7937819388795907350372739 11906729083193861025559109)
                    ·
                      refine ⟨2232511703098848942292333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11906729083193861025559109 2232511703098848942292333)
                      ·
                        rfl

theorem cell23_4347801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_4347801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347801 prefixEnd_4347801 := by exact prefixLift 4347801
  have htrace : WordTrace (prefixWord ++ tailWord_4347801) baseStart_4347801 baseEnd_4347801 := by
    simpa [prefixWord, tailWord_4347801, baseEnd_4347801] using wordTrace_append hprefix tailTrace_4347801
  have hstable : (prefixWord ++ tailWord_4347801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347801).length < 2 ^ (prefixWord ++ tailWord_4347801).sum := by decide
  have hdescent : baseEnd_4347801 < baseStart_4347801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347891 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 4]
def baseStart_4347891 : Nat := 118140960795 + 4347891 * 2 ^ 59
def prefixEnd_4347891 : Nat := 4983230072969 + 3 ^ 40 * 4347891 * 2
def baseEnd_4347891 : Nat := 2232557916357753590166919

theorem tailTrace_4347891 : CollatzResearch.WordTrace tailWord_4347891 prefixEnd_4347891 2232557916357753590166919 := by
  unfold tailWord_4347891
  simp only [CollatzResearch.WordTrace]
  refine ⟨158580612691340942509635527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105720408460893961673090351 158580612691340942509635527)
  ·
    refine ⟨237870919037011413764453291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158580612691340942509635527 237870919037011413764453291)
    ·
      refine ⟨356806378555517120646679937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237870919037011413764453291 356806378555517120646679937)
      ·
        refine ⟨267604783916637840485009953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356806378555517120646679937 267604783916637840485009953)
        ·
          refine ⟨200703587937478380363757465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267604783916637840485009953 200703587937478380363757465)
          ·
            refine ⟨150527690953108785272818099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200703587937478380363757465 150527690953108785272818099)
            ·
              refine ⟨225791536429663177909227149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150527690953108785272818099 225791536429663177909227149)
              ·
                refine ⟨84671826161123691715960181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225791536429663177909227149 84671826161123691715960181)
                ·
                  refine ⟨7937983702605346098371267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84671826161123691715960181 7937983702605346098371267)
                  ·
                    refine ⟨11906975553908019147556901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7937983702605346098371267 11906975553908019147556901)
                    ·
                      refine ⟨2232557916357753590166919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11906975553908019147556901 2232557916357753590166919)
                      ·
                        rfl

theorem cell23_4347891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_4347891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347891 prefixEnd_4347891 := by exact prefixLift 4347891
  have htrace : WordTrace (prefixWord ++ tailWord_4347891) baseStart_4347891 baseEnd_4347891 := by
    simpa [prefixWord, tailWord_4347891, baseEnd_4347891] using wordTrace_append hprefix tailTrace_4347891
  have hstable : (prefixWord ++ tailWord_4347891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347891).length < 2 ^ (prefixWord ++ tailWord_4347891).sum := by decide
  have hdescent : baseEnd_4347891 < baseStart_4347891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347902 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4347902 : Nat := 118140960795 + 4347902 * 2 ^ 59
def prefixEnd_4347902 : Nat := 4983230072969 + 3 ^ 40 * 4347902 * 2
def baseEnd_4347902 : Nat := 2232563564644953047129369

theorem tailTrace_4347902 : CollatzResearch.WordTrace tailWord_4347902 prefixEnd_4347902 2232563564644953047129369 := by
  unfold tailWord_4347902
  simp only [CollatzResearch.WordTrace]
  refine ⟨19822626736787636423535745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105720675929534060925523973 19822626736787636423535745)
  ·
    refine ⟨14866970052590727317651809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19822626736787636423535745 14866970052590727317651809)
    ·
      refine ⟨11150227539443045488238857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14866970052590727317651809 11150227539443045488238857)
      ·
        refine ⟨8362670654582284116179143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11150227539443045488238857 8362670654582284116179143)
        ·
          refine ⟨12544005981873426174268715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8362670654582284116179143 12544005981873426174268715)
          ·
            refine ⟨18816008972810139261403073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12544005981873426174268715 18816008972810139261403073)
            ·
              refine ⟨14112006729607604446052305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18816008972810139261403073 14112006729607604446052305)
              ·
                refine ⟨10584005047205703334539229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14112006729607604446052305 10584005047205703334539229)
                ·
                  refine ⟨3969001892702138750452211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10584005047205703334539229 3969001892702138750452211)
                  ·
                    refine ⟨5953502839053208125678317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3969001892702138750452211 5953502839053208125678317)
                    ·
                      refine ⟨2232563564644953047129369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5953502839053208125678317 2232563564644953047129369)
                      ·
                        rfl

theorem cell23_4347902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4347902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347902 prefixEnd_4347902 := by exact prefixLift 4347902
  have htrace : WordTrace (prefixWord ++ tailWord_4347902) baseStart_4347902 baseEnd_4347902 := by
    simpa [prefixWord, tailWord_4347902, baseEnd_4347902] using wordTrace_append hprefix tailTrace_4347902
  have hstable : (prefixWord ++ tailWord_4347902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347902).length < 2 ^ (prefixWord ++ tailWord_4347902).sum := by decide
  have hdescent : baseEnd_4347902 < baseStart_4347902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347918 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_4347918 : Nat := 118140960795 + 4347918 * 2 ^ 59
def prefixEnd_4347918 : Nat := 4983230072969 + 3 ^ 40 * 4347918 * 2
def baseEnd_4347918 : Nat := 744190593445141661509765

theorem tailTrace_4347918 : CollatzResearch.WordTrace tailWord_4347918 prefixEnd_4347918 744190593445141661509765 := by
  unfold tailWord_4347918
  simp only [CollatzResearch.WordTrace]
  refine ⟨19822699682780390765108551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105721064974828750747245605 19822699682780390765108551)
  ·
    refine ⟨29734049524170586147662827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19822699682780390765108551 29734049524170586147662827)
    ·
      refine ⟨44601074286255879221494241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29734049524170586147662827 44601074286255879221494241)
      ·
        refine ⟨33450805714691909416120681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44601074286255879221494241 33450805714691909416120681)
        ·
          refine ⟨25088104286018932062090511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33450805714691909416120681 25088104286018932062090511)
          ·
            refine ⟨37632156429028398093135767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25088104286018932062090511 37632156429028398093135767)
            ·
              refine ⟨56448234643542597139703651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37632156429028398093135767 56448234643542597139703651)
              ·
                refine ⟨84672351965313895709555477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56448234643542597139703651 84672351965313895709555477)
                ·
                  refine ⟨3969016498374088861385413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84672351965313895709555477 3969016498374088861385413)
                  ·
                    refine ⟨744190593445141661509765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3969016498374088861385413 744190593445141661509765)
                    ·
                      rfl

theorem cell23_4347918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_4347918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347918 prefixEnd_4347918 := by exact prefixLift 4347918
  have htrace : WordTrace (prefixWord ++ tailWord_4347918) baseStart_4347918 baseEnd_4347918 := by
    simpa [prefixWord, tailWord_4347918, baseEnd_4347918] using wordTrace_append hprefix tailTrace_4347918
  have hstable : (prefixWord ++ tailWord_4347918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347918).length < 2 ^ (prefixWord ++ tailWord_4347918).sum := by decide
  have hdescent : baseEnd_4347918 < baseStart_4347918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347928 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4347928 : Nat := 118140960795 + 4347928 * 2 ^ 59
def prefixEnd_4347928 : Nat := 4983230072969 + 3 ^ 40 * 4347928 * 2
def baseEnd_4347928 : Nat := 2232576915141969945404249

theorem tailTrace_4347928 : CollatzResearch.WordTrace tailWord_4347928 prefixEnd_4347928 2232576915141969945404249 := by
  unfold tailWord_4347928
  simp only [CollatzResearch.WordTrace]
  refine ⟨79290981096103448914366219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105721308128137931885821625 79290981096103448914366219)
  ·
    refine ⟨118936471644155173371549329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79290981096103448914366219 118936471644155173371549329)
    ·
      refine ⟨89202353733116380028661997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118936471644155173371549329 89202353733116380028661997)
      ·
        refine ⟨33450882649918642510748249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89202353733116380028661997 33450882649918642510748249)
        ·
          refine ⟨25088161987438981883061187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33450882649918642510748249 25088161987438981883061187)
          ·
            refine ⟨37632242981158472824591781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25088161987438981883061187 37632242981158472824591781)
            ·
              refine ⟨7056045558967213654610959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37632242981158472824591781 7056045558967213654610959)
              ·
                refine ⟨10584068338450820481916439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7056045558967213654610959 10584068338450820481916439)
                ·
                  refine ⟨15876102507676230722874659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10584068338450820481916439 15876102507676230722874659)
                  ·
                    refine ⟨23814153761514346084311989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15876102507676230722874659 23814153761514346084311989)
                    ·
                      refine ⟨2232576915141969945404249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23814153761514346084311989 2232576915141969945404249)
                      ·
                        rfl

theorem cell23_4347928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4347928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347928 prefixEnd_4347928 := by exact prefixLift 4347928
  have htrace : WordTrace (prefixWord ++ tailWord_4347928) baseStart_4347928 baseEnd_4347928 := by
    simpa [prefixWord, tailWord_4347928, baseEnd_4347928] using wordTrace_append hprefix tailTrace_4347928
  have hstable : (prefixWord ++ tailWord_4347928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347928).length < 2 ^ (prefixWord ++ tailWord_4347928).sum := by decide
  have hdescent : baseEnd_4347928 < baseStart_4347928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347952 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 2, 4]
def baseStart_4347952 : Nat := 118140960795 + 4347952 * 2 ^ 59
def prefixEnd_4347952 : Nat := 4983230072969 + 3 ^ 40 * 4347952 * 2
def baseEnd_4347952 : Nat := 744196412892559283834713

theorem tailTrace_4347952 : CollatzResearch.WordTrace tailWord_4347952 prefixEnd_4347952 744196412892559283834713 := by
  unfold tailWord_4347952
  simp only [CollatzResearch.WordTrace]
  refine ⟨79291418772059974963803055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105721891696079966618404073 79291418772059974963803055)
  ·
    refine ⟨118937128158089962445704583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79291418772059974963803055 118937128158089962445704583)
    ·
      refine ⟨178405692237134943668556875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118937128158089962445704583 178405692237134943668556875)
      ·
        refine ⟨267608538355702415502835313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178405692237134943668556875 267608538355702415502835313)
        ·
          refine ⟨200706403766776811627126485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267608538355702415502835313 200706403766776811627126485)
          ·
            refine ⟨4704056338283831522510777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 200706403766776811627126485 4704056338283831522510777)
            ·
              refine ⟨3528042253712873641883083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4704056338283831522510777 3528042253712873641883083)
              ·
                refine ⟨5292063380569310462824625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528042253712873641883083 5292063380569310462824625)
                ·
                  refine ⟨3969047535426982847118469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5292063380569310462824625 3969047535426982847118469)
                  ·
                    refine ⟨744196412892559283834713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3969047535426982847118469 744196412892559283834713)
                    ·
                      rfl

theorem cell23_4347952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 4].length) (baseStart_4347952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347952 prefixEnd_4347952 := by exact prefixLift 4347952
  have htrace : WordTrace (prefixWord ++ tailWord_4347952) baseStart_4347952 baseEnd_4347952 := by
    simpa [prefixWord, tailWord_4347952, baseEnd_4347952] using wordTrace_append hprefix tailTrace_4347952
  have hstable : (prefixWord ++ tailWord_4347952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347952).length < 2 ^ (prefixWord ++ tailWord_4347952).sum := by decide
  have hdescent : baseEnd_4347952 < baseStart_4347952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347971 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_4347971 : Nat := 118140960795 + 4347971 * 2 ^ 59
def prefixEnd_4347971 : Nat := 4983230072969 + 3 ^ 40 * 4347971 * 2
def baseEnd_4347971 : Nat := 2232598994810113277166551

theorem tailTrace_4347971 : CollatzResearch.WordTrace tailWord_4347971 prefixEnd_4347971 2232598994810113277166551 := by
  unfold tailWord_4347971
  simp only [CollatzResearch.WordTrace]
  refine ⟨158583530531051116172547767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105722353687367410781698511 158583530531051116172547767)
  ·
    refine ⟨237875295796576674258821651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158583530531051116172547767 237875295796576674258821651)
    ·
      refine ⟨356812943694865011388232477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237875295796576674258821651 356812943694865011388232477)
      ·
        refine ⟨133804853885574379270587179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356812943694865011388232477 133804853885574379270587179)
        ·
          refine ⟨200707280828361568905880769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133804853885574379270587179 200707280828361568905880769)
          ·
            refine ⟨150530460621271176679410577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200707280828361568905880769 150530460621271176679410577)
            ·
              refine ⟨112897845465953382509557933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150530460621271176679410577 112897845465953382509557933)
              ·
                refine ⟨42336692049732518441084225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112897845465953382509557933 42336692049732518441084225)
                ·
                  refine ⟨31752519037299388830813169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42336692049732518441084225 31752519037299388830813169)
                  ·
                    refine ⟨23814389277974541623109877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31752519037299388830813169 23814389277974541623109877)
                    ·
                      refine ⟨2232598994810113277166551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23814389277974541623109877 2232598994810113277166551)
                      ·
                        rfl

theorem cell23_4347971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_4347971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347971 prefixEnd_4347971 := by exact prefixLift 4347971
  have htrace : WordTrace (prefixWord ++ tailWord_4347971) baseStart_4347971 baseEnd_4347971 := by
    simpa [prefixWord, tailWord_4347971, baseEnd_4347971] using wordTrace_append hprefix tailTrace_4347971
  have hstable : (prefixWord ++ tailWord_4347971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347971).length < 2 ^ (prefixWord ++ tailWord_4347971).sum := by decide
  have hdescent : baseEnd_4347971 < baseStart_4347971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4347992 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_4347992 : Nat := 118140960795 + 4347992 * 2 ^ 59
def prefixEnd_4347992 : Nat := 4983230072969 + 3 ^ 40 * 4347992 * 2
def baseEnd_4347992 : Nat := 2232609777903857695003955

theorem tailTrace_4347992 : CollatzResearch.WordTrace tailWord_4347992 prefixEnd_4347992 2232609777903857695003955 := by
  unfold tailWord_4347992
  simp only [CollatzResearch.WordTrace]
  refine ⟨79292148231987518379531115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105722864309316691172708153 79292148231987518379531115)
  ·
    refine ⟨118938222347981277569296673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79292148231987518379531115 118938222347981277569296673)
    ·
      refine ⟨89203666760985958176972505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118938222347981277569296673 89203666760985958176972505)
      ·
        refine ⟨66902750070739468632729379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89203666760985958176972505 66902750070739468632729379)
        ·
          refine ⟨100354125106109202949094069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66902750070739468632729379 100354125106109202949094069)
          ·
            refine ⟨9408199228697737776477569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100354125106109202949094069 9408199228697737776477569)
            ·
              refine ⟨7056149421523303332358177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9408199228697737776477569 7056149421523303332358177)
              ·
                refine ⟨5292112066142477499268633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7056149421523303332358177 5292112066142477499268633)
                ·
                  refine ⟨3969084049606858124451475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5292112066142477499268633 3969084049606858124451475)
                  ·
                    refine ⟨5953626074410287186677213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3969084049606858124451475 5953626074410287186677213)
                    ·
                      refine ⟨2232609777903857695003955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5953626074410287186677213 2232609777903857695003955)
                      ·
                        rfl

theorem cell23_4347992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_4347992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4347992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4347992 prefixEnd_4347992 := by exact prefixLift 4347992
  have htrace : WordTrace (prefixWord ++ tailWord_4347992) baseStart_4347992 baseEnd_4347992 := by
    simpa [prefixWord, tailWord_4347992, baseEnd_4347992] using wordTrace_append hprefix tailTrace_4347992
  have hstable : (prefixWord ++ tailWord_4347992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4347992).length < 2 ^ (prefixWord ++ tailWord_4347992).sum := by decide
  have hdescent : baseEnd_4347992 < baseStart_4347992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4347992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348015 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 1, 4, 2]
def baseStart_4348015 : Nat := 118140960795 + 4348015 * 2 ^ 59
def prefixEnd_4348015 : Nat := 4983230072969 + 3 ^ 40 * 4348015 * 2
def baseEnd_4348015 : Nat := 2232621587958911105016349

theorem tailTrace_4348015 : CollatzResearch.WordTrace tailWord_4348015 prefixEnd_4348015 2232621587958911105016349 := by
  unfold tailWord_4348015
  simp only [CollatzResearch.WordTrace]
  refine ⟨158585135342891711687149499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105723423561927807791432999 158585135342891711687149499)
  ·
    refine ⟨237877703014337567530724249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158585135342891711687149499 237877703014337567530724249)
    ·
      refine ⟨178408277260753175648043187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237877703014337567530724249 178408277260753175648043187)
      ·
        refine ⟨267612415891129763472064781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178408277260753175648043187 267612415891129763472064781)
        ·
          refine ⟨100354655959173661302024293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267612415891129763472064781 100354655959173661302024293)
          ·
            refine ⟨18816497992345061494129555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100354655959173661302024293 18816497992345061494129555)
            ·
              refine ⟨28224746988517592241194333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18816497992345061494129555 28224746988517592241194333)
              ·
                refine ⟨10584280120694097090447875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28224746988517592241194333 10584280120694097090447875)
                ·
                  refine ⟨15876420181041145635671813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10584280120694097090447875 15876420181041145635671813)
                  ·
                    refine ⟨2976828783945214806688465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15876420181041145635671813 2976828783945214806688465)
                    ·
                      refine ⟨2232621587958911105016349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976828783945214806688465 2232621587958911105016349)
                      ·
                        rfl

theorem cell23_4348015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4, 2].length) (baseStart_4348015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348015 prefixEnd_4348015 := by exact prefixLift 4348015
  have htrace : WordTrace (prefixWord ++ tailWord_4348015) baseStart_4348015 baseEnd_4348015 := by
    simpa [prefixWord, tailWord_4348015, baseEnd_4348015] using wordTrace_append hprefix tailTrace_4348015
  have hstable : (prefixWord ++ tailWord_4348015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348015).length < 2 ^ (prefixWord ++ tailWord_4348015).sum := by decide
  have hdescent : baseEnd_4348015 < baseStart_4348015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348048 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_4348048 : Nat := 118140960795 + 4348048 * 2 ^ 59
def prefixEnd_4348048 : Nat := 4983230072969 + 3 ^ 40 * 4348048 * 2
def baseEnd_4348048 : Nat := 2232638532820509475903697

theorem tailTrace_4348048 : CollatzResearch.WordTrace tailWord_4348048 prefixEnd_4348048 2232638532820509475903697 := by
  unfold tailWord_4348048
  simp only [CollatzResearch.WordTrace]
  refine ⟨79293169475886079161550399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105724225967848105548733865 79293169475886079161550399)
  ·
    refine ⟨118939754213829118742325599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79293169475886079161550399 118939754213829118742325599)
    ·
      refine ⟨178409631320743678113488399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118939754213829118742325599 178409631320743678113488399)
      ·
        refine ⟨267614446981115517170232599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178409631320743678113488399 267614446981115517170232599)
        ·
          refine ⟨401421670471673275755348899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267614446981115517170232599 401421670471673275755348899)
          ·
            refine ⟨602132505707509913633023349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401421670471673275755348899 602132505707509913633023349)
            ·
              refine ⟨56449922410079054403095939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 602132505707509913633023349 56449922410079054403095939)
              ·
                refine ⟨84674883615118581604643909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56449922410079054403095939 84674883615118581604643909)
                ·
                  refine ⟨15876540677834734050870733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84674883615118581604643909 15876540677834734050870733)
                  ·
                    refine ⟨5953702754188025269076525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15876540677834734050870733 5953702754188025269076525)
                    ·
                      refine ⟨2232638532820509475903697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5953702754188025269076525 2232638532820509475903697)
                      ·
                        rfl

theorem cell23_4348048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_4348048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348048 prefixEnd_4348048 := by exact prefixLift 4348048
  have htrace : WordTrace (prefixWord ++ tailWord_4348048) baseStart_4348048 baseEnd_4348048 := by
    simpa [prefixWord, tailWord_4348048, baseEnd_4348048] using wordTrace_append hprefix tailTrace_4348048
  have hstable : (prefixWord ++ tailWord_4348048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348048).length < 2 ^ (prefixWord ++ tailWord_4348048).sum := by decide
  have hdescent : baseEnd_4348048 < baseStart_4348048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348055 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 7]
def baseStart_4348055 : Nat := 118140960795 + 4348055 * 2 ^ 59
def prefixEnd_4348055 : Nat := 4983230072969 + 3 ^ 40 * 4348055 * 2
def baseEnd_4348055 : Nat := 248071347465010105390685

theorem tailTrace_4348055 : CollatzResearch.WordTrace tailWord_4348055 prefixEnd_4348055 248071347465010105390685 := by
  unfold tailWord_4348055
  simp only [CollatzResearch.WordTrace]
  refine ⟨158586594262746798518605619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105724396175164532345737079 158586594262746798518605619)
  ·
    refine ⟨237879891394120197777908429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158586594262746798518605619 237879891394120197777908429)
    ·
      refine ⟨89204959272795074166715661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237879891394120197777908429 89204959272795074166715661)
      ·
        refine ⟨33451859727298152812518373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89204959272795074166715661 33451859727298152812518373)
        ·
          refine ⟨6272223698868403652347195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33451859727298152812518373 6272223698868403652347195)
          ·
            refine ⟨9408335548302605478520793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6272223698868403652347195 9408335548302605478520793)
            ·
              refine ⟨7056251661226954108890595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9408335548302605478520793 7056251661226954108890595)
              ·
                refine ⟨10584377491840431163335893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7056251661226954108890595 10584377491840431163335893)
                ·
                  refine ⟨248071347465010105390685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10584377491840431163335893 248071347465010105390685)
                  ·
                    rfl

theorem cell23_4348055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 7].length) (baseStart_4348055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348055 prefixEnd_4348055 := by exact prefixLift 4348055
  have htrace : WordTrace (prefixWord ++ tailWord_4348055) baseStart_4348055 baseEnd_4348055 := by
    simpa [prefixWord, tailWord_4348055, baseEnd_4348055] using wordTrace_append hprefix tailTrace_4348055
  have hstable : (prefixWord ++ tailWord_4348055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348055).length < 2 ^ (prefixWord ++ tailWord_4348055).sum := by decide
  have hdescent : baseEnd_4348055 < baseStart_4348055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348065 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4348065 : Nat := 118140960795 + 4348065 * 2 ^ 59
def prefixEnd_4348065 : Nat := 4983230072969 + 3 ^ 40 * 4348065 * 2
def baseEnd_4348065 : Nat := 2232647261991635909391119

theorem tailTrace_4348065 : CollatzResearch.WordTrace tailWord_4348065 prefixEnd_4348065 2232647261991635909391119 := by
  unfold tailWord_4348065
  simp only [CollatzResearch.WordTrace]
  refine ⟨158586958992710570226469649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105724639328473713484313099 158586958992710570226469649)
  ·
    refine ⟨118940219244532927669852237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158586958992710570226469649 118940219244532927669852237)
    ·
      refine ⟨44602582216699847876194589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118940219244532927669852237 44602582216699847876194589)
      ·
        refine ⟨16725968331262442953572971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44602582216699847876194589 16725968331262442953572971)
        ·
          refine ⟨25088952496893664430359457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16725968331262442953572971 25088952496893664430359457)
          ·
            refine ⟨18816714372670248322769593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25088952496893664430359457 18816714372670248322769593)
            ·
              refine ⟨14112535779502686242077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18816714372670248322769593 14112535779502686242077195)
              ·
                refine ⟨21168803669254029363115793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14112535779502686242077195 21168803669254029363115793)
                ·
                  refine ⟨15876602751940522022336845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21168803669254029363115793 15876602751940522022336845)
                  ·
                    refine ⟨5953726031977695758376317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15876602751940522022336845 5953726031977695758376317)
                    ·
                      refine ⟨2232647261991635909391119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5953726031977695758376317 2232647261991635909391119)
                      ·
                        rfl

theorem cell23_4348065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4348065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348065 prefixEnd_4348065 := by exact prefixLift 4348065
  have htrace : WordTrace (prefixWord ++ tailWord_4348065) baseStart_4348065 baseEnd_4348065 := by
    simpa [prefixWord, tailWord_4348065, baseEnd_4348065] using wordTrace_append hprefix tailTrace_4348065
  have hstable : (prefixWord ++ tailWord_4348065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348065).length < 2 ^ (prefixWord ++ tailWord_4348065).sum := by decide
  have hdescent : baseEnd_4348065 < baseStart_4348065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348088 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_4348088 : Nat := 118140960795 + 4348088 * 2 ^ 59
def prefixEnd_4348088 : Nat := 4983230072969 + 3 ^ 40 * 4348088 * 2
def baseEnd_4348088 : Nat := 2232659072046689319403513

theorem tailTrace_4348088 : CollatzResearch.WordTrace tailWord_4348088 prefixEnd_4348088 2232659072046689319403513 := by
  unfold tailWord_4348088
  simp only [CollatzResearch.WordTrace]
  refine ⟨79293898935813622577278459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105725198581084830103037945 79293898935813622577278459)
  ·
    refine ⟨118940848403720433865917689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79293898935813622577278459 118940848403720433865917689)
    ·
      refine ⟨89205636302790325399438267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118940848403720433865917689 89205636302790325399438267)
      ·
        refine ⟨133808454454185488099157401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89205636302790325399438267 133808454454185488099157401)
        ·
          refine ⟨100356340840639116074368051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133808454454185488099157401 100356340840639116074368051)
          ·
            refine ⟨150534511260958674111552077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100356340840639116074368051 150534511260958674111552077)
            ·
              refine ⟨56450441722859502791832029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150534511260958674111552077 56450441722859502791832029)
              ·
                refine ⟨21168915646072313546937011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56450441722859502791832029 21168915646072313546937011)
                ·
                  refine ⟨31753373469108470320405517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21168915646072313546937011 31753373469108470320405517)
                  ·
                    refine ⟨11907515050915676370152069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31753373469108470320405517 11907515050915676370152069)
                    ·
                      refine ⟨2232659072046689319403513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11907515050915676370152069 2232659072046689319403513)
                      ·
                        rfl

theorem cell23_4348088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_4348088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348088 prefixEnd_4348088 := by exact prefixLift 4348088
  have htrace : WordTrace (prefixWord ++ tailWord_4348088) baseStart_4348088 baseEnd_4348088 := by
    simpa [prefixWord, tailWord_4348088, baseEnd_4348088] using wordTrace_append hprefix tailTrace_4348088
  have hstable : (prefixWord ++ tailWord_4348088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348088).length < 2 ^ (prefixWord ++ tailWord_4348088).sum := by decide
  have hdescent : baseEnd_4348088 < baseStart_4348088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348105 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 2, 4, 2]
def baseStart_4348105 : Nat := 118140960795 + 4348105 * 2 ^ 59
def prefixEnd_4348105 : Nat := 4983230072969 + 3 ^ 40 * 4348105 * 2
def baseEnd_4348105 : Nat := 2232667801217815752890935

theorem tailTrace_4348105 : CollatzResearch.WordTrace tailWord_4348105 prefixEnd_4348105 2232667801217815752890935 := by
  unfold tailWord_4348105
  simp only [CollatzResearch.WordTrace]
  refine ⟨158588417912565657057925769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105725611941710438038617179 158588417912565657057925769)
  ·
    refine ⟨118941313434424242793444327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158588417912565657057925769 118941313434424242793444327)
    ·
      refine ⟨178411970151636364190166491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118941313434424242793444327 178411970151636364190166491)
      ·
        refine ⟨267617955227454546285249737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178411970151636364190166491 267617955227454546285249737)
        ·
          refine ⟨200713466420590909713937303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267617955227454546285249737 200713466420590909713937303)
          ·
            refine ⟨301070199630886364570905955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200713466420590909713937303 301070199630886364570905955)
            ·
              refine ⟨451605299446329546856358933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301070199630886364570905955 451605299446329546856358933)
              ·
                refine ⟨21168998411546697508891825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 451605299446329546856358933 21168998411546697508891825)
                ·
                  refine ⟨15876748808660023131668869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21168998411546697508891825 15876748808660023131668869)
                  ·
                    refine ⟨2976890401623754337187913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15876748808660023131668869 2976890401623754337187913)
                    ·
                      refine ⟨2232667801217815752890935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976890401623754337187913 2232667801217815752890935)
                      ·
                        rfl

theorem cell23_4348105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 4, 2].length) (baseStart_4348105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348105 prefixEnd_4348105 := by exact prefixLift 4348105
  have htrace : WordTrace (prefixWord ++ tailWord_4348105) baseStart_4348105 baseEnd_4348105 := by
    simpa [prefixWord, tailWord_4348105, baseEnd_4348105] using wordTrace_append hprefix tailTrace_4348105
  have hstable : (prefixWord ++ tailWord_4348105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348105).length < 2 ^ (prefixWord ++ tailWord_4348105).sum := by decide
  have hdescent : baseEnd_4348105 < baseStart_4348105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348162 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_4348162 : Nat := 118140960795 + 4348162 * 2 ^ 59
def prefixEnd_4348162 : Nat := 4983230072969 + 3 ^ 40 * 4348162 * 2
def baseEnd_4348162 : Nat := 248077452179458003319797

theorem tailTrace_4348162 : CollatzResearch.WordTrace tailWord_4348162 prefixEnd_4348162 248077452179458003319797 := by
  unfold tailWord_4348162
  simp only [CollatzResearch.WordTrace]
  refine ⟨39647624218339788948187685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105726997915572770528500493 39647624218339788948187685)
  ·
    refine ⟨7433929540938710427785191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39647624218339788948187685 7433929540938710427785191)
    ·
      refine ⟨11150894311408065641677787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7433929540938710427785191 11150894311408065641677787)
      ·
        refine ⟨16726341467112098462516681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11150894311408065641677787 16726341467112098462516681)
        ·
          refine ⟨12544756100334073846887511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16726341467112098462516681 12544756100334073846887511)
          ·
            refine ⟨18817134150501110770331267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12544756100334073846887511 18817134150501110770331267)
            ·
              refine ⟨28225701225751666155496901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18817134150501110770331267 28225701225751666155496901)
              ·
                refine ⟨5292318979828437404155669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28225701225751666155496901 5292318979828437404155669)
                ·
                  refine ⟨248077452179458003319797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5292318979828437404155669 248077452179458003319797)
                  ·
                    rfl

theorem cell23_4348162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_4348162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348162 prefixEnd_4348162 := by exact prefixLift 4348162
  have htrace : WordTrace (prefixWord ++ tailWord_4348162) baseStart_4348162 baseEnd_4348162 := by
    simpa [prefixWord, tailWord_4348162, baseEnd_4348162] using wordTrace_append hprefix tailTrace_4348162
  have hstable : (prefixWord ++ tailWord_4348162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348162).length < 2 ^ (prefixWord ++ tailWord_4348162).sum := by decide
  have hdescent : baseEnd_4348162 < baseStart_4348162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348172 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_4348172 : Nat := 118140960795 + 4348172 * 2 ^ 59
def prefixEnd_4348172 : Nat := 4983230072969 + 3 ^ 40 * 4348172 * 2
def baseEnd_4348172 : Nat := 2232702204421666990753127

theorem tailTrace_4348172 : CollatzResearch.WordTrace tailWord_4348172 prefixEnd_4348172 2232702204421666990753127 := by
  unfold tailWord_4348172
  simp only [CollatzResearch.WordTrace]
  refine ⟨79295430801661463750307385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105727241068881951667076513 79295430801661463750307385)
  ·
    refine ⟨59471573101246097812730539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79295430801661463750307385 59471573101246097812730539)
    ·
      refine ⟨89207359651869146719095809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59471573101246097812730539 89207359651869146719095809)
      ·
        refine ⟨66905519738901860039321857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89207359651869146719095809 66905519738901860039321857)
        ·
          refine ⟨50179139804176395029491393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66905519738901860039321857 50179139804176395029491393)
          ·
            refine ⟨37634354853132296272118545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50179139804176395029491393 37634354853132296272118545)
            ·
              refine ⟨28225766139849222204088909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37634354853132296272118545 28225766139849222204088909)
              ·
                refine ⟨10584662302443458326533341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28225766139849222204088909 10584662302443458326533341)
                ·
                  refine ⟨3969248363416296872450003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10584662302443458326533341 3969248363416296872450003)
                  ·
                    refine ⟨5953872545124445308675005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3969248363416296872450003 5953872545124445308675005)
                    ·
                      refine ⟨2232702204421666990753127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5953872545124445308675005 2232702204421666990753127)
                      ·
                        rfl

theorem cell23_4348172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_4348172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348172 prefixEnd_4348172 := by exact prefixLift 4348172
  have htrace : WordTrace (prefixWord ++ tailWord_4348172) baseStart_4348172 baseEnd_4348172 := by
    simpa [prefixWord, tailWord_4348172, baseEnd_4348172] using wordTrace_append hprefix tailTrace_4348172
  have hstable : (prefixWord ++ tailWord_4348172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348172).length < 2 ^ (prefixWord ++ tailWord_4348172).sum := by decide
  have hdescent : baseEnd_4348172 < baseStart_4348172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348195 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 4]
def baseStart_4348195 : Nat := 118140960795 + 4348195 * 2 ^ 59
def prefixEnd_4348195 : Nat := 4983230072969 + 3 ^ 40 * 4348195 * 2
def baseEnd_4348195 : Nat := 2232714014476720400765521

theorem tailTrace_4348195 : CollatzResearch.WordTrace tailWord_4348195 prefixEnd_4348195 2232714014476720400765521 := by
  unfold tailWord_4348195
  simp only [CollatzResearch.WordTrace]
  refine ⟨158591700482239602428702039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105727800321493068285801359 158591700482239602428702039)
  ·
    refine ⟨237887550723359403643053059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158591700482239602428702039 237887550723359403643053059)
    ·
      refine ⟨356831326085039105464579589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237887550723359403643053059 356831326085039105464579589)
      ·
        refine ⟨66905873640944832274608673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 356831326085039105464579589 66905873640944832274608673)
        ·
          refine ⟨50179405230708624205956505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66905873640944832274608673 50179405230708624205956505)
          ·
            refine ⟨37634553923031468154467379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50179405230708624205956505 37634553923031468154467379)
            ·
              refine ⟨56451830884547202231701069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37634553923031468154467379 56451830884547202231701069)
              ·
                refine ⟨21169436581705200836887901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56451830884547202231701069 21169436581705200836887901)
                ·
                  refine ⟨7938538718139450313832963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21169436581705200836887901 7938538718139450313832963)
                  ·
                    refine ⟨11907808077209175470749445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7938538718139450313832963 11907808077209175470749445)
                    ·
                      refine ⟨2232714014476720400765521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11907808077209175470749445 2232714014476720400765521)
                      ·
                        rfl

theorem cell23_4348195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_4348195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348195 prefixEnd_4348195 := by exact prefixLift 4348195
  have htrace : WordTrace (prefixWord ++ tailWord_4348195) baseStart_4348195 baseEnd_4348195 := by
    simpa [prefixWord, tailWord_4348195, baseEnd_4348195] using wordTrace_append hprefix tailTrace_4348195
  have hstable : (prefixWord ++ tailWord_4348195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348195).length < 2 ^ (prefixWord ++ tailWord_4348195).sum := by decide
  have hdescent : baseEnd_4348195 < baseStart_4348195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348242 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_4348242 : Nat := 118140960795 + 4348242 * 2 ^ 59
def prefixEnd_4348242 : Nat := 4983230072969 + 3 ^ 40 * 4348242 * 2
def baseEnd_4348242 : Nat := 2232738148067481716877805

theorem tailTrace_4348242 : CollatzResearch.WordTrace tailWord_4348242 prefixEnd_4348242 2232738148067481716877805 := by
  unfold tailWord_4348242
  simp only [CollatzResearch.WordTrace]
  refine ⟨39648353678267332363915745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105728943142046219637108653 39648353678267332363915745)
  ·
    refine ⟨29736265258700499272936809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39648353678267332363915745 29736265258700499272936809)
    ·
      refine ⟨22302198944025374454702607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29736265258700499272936809 22302198944025374454702607)
      ·
        refine ⟨33453298416038061682053911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22302198944025374454702607 33453298416038061682053911)
        ·
          refine ⟨50179947624057092523080867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33453298416038061682053911 50179947624057092523080867)
          ·
            refine ⟨75269921436085638784621301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50179947624057092523080867 75269921436085638784621301)
            ·
              refine ⟨7056555134633028636058247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75269921436085638784621301 7056555134633028636058247)
              ·
                refine ⟨10584832701949542954087371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7056555134633028636058247 10584832701949542954087371)
                ·
                  refine ⟨15877249052924314431131057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10584832701949542954087371 15877249052924314431131057)
                  ·
                    refine ⟨11907936789693235823348293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15877249052924314431131057 11907936789693235823348293)
                    ·
                      refine ⟨2232738148067481716877805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11907936789693235823348293 2232738148067481716877805)
                      ·
                        rfl

theorem cell23_4348242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_4348242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348242 prefixEnd_4348242 := by exact prefixLift 4348242
  have htrace : WordTrace (prefixWord ++ tailWord_4348242) baseStart_4348242 baseEnd_4348242 := by
    simpa [prefixWord, tailWord_4348242, baseEnd_4348242] using wordTrace_append hprefix tailTrace_4348242
  have hstable : (prefixWord ++ tailWord_4348242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348242).length < 2 ^ (prefixWord ++ tailWord_4348242).sum := by decide
  have hdescent : baseEnd_4348242 < baseStart_4348242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348263 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_4348263 : Nat := 118140960795 + 4348263 * 2 ^ 59
def prefixEnd_4348263 : Nat := 4983230072969 + 3 ^ 40 * 4348263 * 2
def baseEnd_4348263 : Nat := 2232748931161226134715209

theorem tailTrace_4348263 : CollatzResearch.WordTrace tailWord_4348263 prefixEnd_4348263 2232748931161226134715209 := by
  unfold tailWord_4348263
  simp only [CollatzResearch.WordTrace]
  refine ⟨158594180645993250042177443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105729453763995500028118295 158594180645993250042177443)
  ·
    refine ⟨237891270968989875063266165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158594180645993250042177443 237891270968989875063266165)
    ·
      refine ⟨22302306653342800787181203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237891270968989875063266165 22302306653342800787181203)
      ·
        refine ⟨33453459980014201180771805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22302306653342800787181203 33453459980014201180771805)
        ·
          refine ⟨12545047492505325442789427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33453459980014201180771805 12545047492505325442789427)
          ·
            refine ⟨18817571238757988164184141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12545047492505325442789427 18817571238757988164184141)
            ·
              refine ⟨7056589214534245561569053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18817571238757988164184141 7056589214534245561569053)
              ·
                refine ⟨2646220955450342085588395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7056589214534245561569053 2646220955450342085588395)
                ·
                  refine ⟨3969331433175513128382593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646220955450342085588395 3969331433175513128382593)
                  ·
                    refine ⟨2976998574881634846286945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3969331433175513128382593 2976998574881634846286945)
                    ·
                      refine ⟨2232748931161226134715209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2976998574881634846286945 2232748931161226134715209)
                      ·
                        rfl

theorem cell23_4348263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_4348263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348263 prefixEnd_4348263 := by exact prefixLift 4348263
  have htrace : WordTrace (prefixWord ++ tailWord_4348263) baseStart_4348263 baseEnd_4348263 := by
    simpa [prefixWord, tailWord_4348263, baseEnd_4348263] using wordTrace_append hprefix tailTrace_4348263
  have hstable : (prefixWord ++ tailWord_4348263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348263).length < 2 ^ (prefixWord ++ tailWord_4348263).sum := by decide
  have hdescent : baseEnd_4348263 < baseStart_4348263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348290 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4348290 : Nat := 118140960795 + 4348290 * 2 ^ 59
def prefixEnd_4348290 : Nat := 4983230072969 + 3 ^ 40 * 4348290 * 2
def baseEnd_4348290 : Nat := 744254265046299176359195

theorem tailTrace_4348290 : CollatzResearch.WordTrace tailWord_4348290 prefixEnd_4348290 744254265046299176359195 := by
  unfold tailWord_4348290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39648791354223858413352581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105730110277930289102273549 39648791354223858413352581)
  ·
    refine ⟨7434148378916973452503609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39648791354223858413352581 7434148378916973452503609)
    ·
      refine ⟨5575611284187730089377707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7434148378916973452503609 5575611284187730089377707)
      ·
        refine ⟨8363416926281595134066561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5575611284187730089377707 8363416926281595134066561)
        ·
          refine ⟨6272562694711196350549921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8363416926281595134066561 6272562694711196350549921)
          ·
            refine ⟨4704422021033397262912441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6272562694711196350549921 4704422021033397262912441)
            ·
              refine ⟨3528316515775047947184331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4704422021033397262912441 3528316515775047947184331)
              ·
                refine ⟨5292474773662571920776497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528316515775047947184331 5292474773662571920776497)
                ·
                  refine ⟨3969356080246928940582373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5292474773662571920776497 3969356080246928940582373)
                  ·
                    refine ⟨744254265046299176359195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3969356080246928940582373 744254265046299176359195)
                    ·
                      rfl

theorem cell23_4348290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4348290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348290 prefixEnd_4348290 := by exact prefixLift 4348290
  have htrace : WordTrace (prefixWord ++ tailWord_4348290) baseStart_4348290 baseEnd_4348290 := by
    simpa [prefixWord, tailWord_4348290, baseEnd_4348290] using wordTrace_append hprefix tailTrace_4348290
  have hstable : (prefixWord ++ tailWord_4348290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348290).length < 2 ^ (prefixWord ++ tailWord_4348290).sum := by decide
  have hdescent : baseEnd_4348290 < baseStart_4348290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348295 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 8]
def baseStart_4348295 : Nat := 118140960795 + 4348295 * 2 ^ 59
def prefixEnd_4348295 : Nat := 4983230072969 + 3 ^ 40 * 4348295 * 2
def baseEnd_4348295 : Nat := 744255120847390003171687

theorem tailTrace_4348295 : CollatzResearch.WordTrace tailWord_4348295 prefixEnd_4348295 744255120847390003171687 := by
  unfold tailWord_4348295
  simp only [CollatzResearch.WordTrace]
  refine ⟨158595347781877319507342339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105730231854584879671561559 158595347781877319507342339)
  ·
    refine ⟨237893021672815979261013509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158595347781877319507342339 237893021672815979261013509)
    ·
      refine ⟨44604941563652996111440033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237893021672815979261013509 44604941563652996111440033)
      ·
        refine ⟨33453706172739747083580025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44604941563652996111440033 33453706172739747083580025)
        ·
          refine ⟨25090279629554810312685019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33453706172739747083580025 25090279629554810312685019)
          ·
            refine ⟨37635419444332215469027529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25090279629554810312685019 37635419444332215469027529)
            ·
              refine ⟨28226564583249161601770647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37635419444332215469027529 28226564583249161601770647)
              ·
                refine ⟨42339846874873742402655971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28226564583249161601770647 42339846874873742402655971)
                ·
                  refine ⟨63509770312310613603983957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42339846874873742402655971 63509770312310613603983957)
                  ·
                    refine ⟨744255120847390003171687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63509770312310613603983957 744255120847390003171687)
                    ·
                      rfl

theorem cell23_4348295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_4348295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348295 prefixEnd_4348295 := by exact prefixLift 4348295
  have htrace : WordTrace (prefixWord ++ tailWord_4348295) baseStart_4348295 baseEnd_4348295 := by
    simpa [prefixWord, tailWord_4348295, baseEnd_4348295] using wordTrace_append hprefix tailTrace_4348295
  have hstable : (prefixWord ++ tailWord_4348295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348295).length < 2 ^ (prefixWord ++ tailWord_4348295).sum := by decide
  have hdescent : baseEnd_4348295 < baseStart_4348295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348319 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4348319 : Nat := 118140960795 + 4348319 * 2 ^ 59
def prefixEnd_4348319 : Nat := 4983230072969 + 3 ^ 40 * 4348319 * 2
def baseEnd_4348319 : Nat := 2232777686077877915614951

theorem tailTrace_4348319 : CollatzResearch.WordTrace tailWord_4348319 prefixEnd_4348319 2232777686077877915614951 := by
  unfold tailWord_4348319
  simp only [CollatzResearch.WordTrace]
  refine ⟨158596223133790371606216011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105730815422526914404144007 158596223133790371606216011)
  ·
    refine ⟨237894334700685557409324017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158596223133790371606216011 237894334700685557409324017)
    ·
      refine ⟨178420751025514168056993013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237894334700685557409324017 178420751025514168056993013)
      ·
        refine ⟨16726945408641953255343095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178420751025514168056993013 16726945408641953255343095)
        ·
          refine ⟨25090418112962929883014643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16726945408641953255343095 25090418112962929883014643)
          ·
            refine ⟨37635627169444394824521965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25090418112962929883014643 37635627169444394824521965)
            ·
              refine ⟨14113360188541648059195737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37635627169444394824521965 14113360188541648059195737)
              ·
                refine ⟨10585020141406236044396803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14113360188541648059195737 10585020141406236044396803)
                ·
                  refine ⟨15877530212109354066595205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10585020141406236044396803 15877530212109354066595205)
                  ·
                    refine ⟨2977036914770503887486601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15877530212109354066595205 2977036914770503887486601)
                    ·
                      refine ⟨2232777686077877915614951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977036914770503887486601 2232777686077877915614951)
                      ·
                        rfl

theorem cell23_4348319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4348319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348319 prefixEnd_4348319 := by exact prefixLift 4348319
  have htrace : WordTrace (prefixWord ++ tailWord_4348319) baseStart_4348319 baseEnd_4348319 := by
    simpa [prefixWord, tailWord_4348319, baseEnd_4348319] using wordTrace_append hprefix tailTrace_4348319
  have hstable : (prefixWord ++ tailWord_4348319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348319).length < 2 ^ (prefixWord ++ tailWord_4348319).sum := by decide
  have hdescent : baseEnd_4348319 < baseStart_4348319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348322 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4348322 : Nat := 118140960795 + 4348322 * 2 ^ 59
def prefixEnd_4348322 : Nat := 4983230072969 + 3 ^ 40 * 4348322 * 2
def baseEnd_4348322 : Nat := 2232779226519841403877437

theorem tailTrace_4348322 : CollatzResearch.WordTrace tailWord_4348322 prefixEnd_4348322 2232779226519841403877437 := by
  unfold tailWord_4348322
  simp only [CollatzResearch.WordTrace]
  refine ⟨39649083138194875779643805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105730888368519668745716813 39649083138194875779643805)
  ·
    refine ⟨14868406176823078417366427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39649083138194875779643805 14868406176823078417366427)
    ·
      refine ⟨22302609265234617626049641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14868406176823078417366427 22302609265234617626049641)
      ·
        refine ⟨16726956948925963219537231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22302609265234617626049641 16726956948925963219537231)
        ·
          refine ⟨25090435423388944829305847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16726956948925963219537231 25090435423388944829305847)
          ·
            refine ⟨37635653135083417243958771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25090435423388944829305847 37635653135083417243958771)
            ·
              refine ⟨56453479702625125865938157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37635653135083417243958771 56453479702625125865938157)
              ·
                refine ⟨21170054888484422199726809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56453479702625125865938157 21170054888484422199726809)
                ·
                  refine ⟨15877541166363316649795107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21170054888484422199726809 15877541166363316649795107)
                  ·
                    refine ⟨23816311749544974974692661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15877541166363316649795107 23816311749544974974692661)
                    ·
                      refine ⟨2232779226519841403877437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23816311749544974974692661 2232779226519841403877437)
                      ·
                        rfl

theorem cell23_4348322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4348322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348322 prefixEnd_4348322 := by exact prefixLift 4348322
  have htrace : WordTrace (prefixWord ++ tailWord_4348322) baseStart_4348322 baseEnd_4348322 := by
    simpa [prefixWord, tailWord_4348322, baseEnd_4348322] using wordTrace_append hprefix tailTrace_4348322
  have hstable : (prefixWord ++ tailWord_4348322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348322).length < 2 ^ (prefixWord ++ tailWord_4348322).sum := by decide
  have hdescent : baseEnd_4348322 < baseStart_4348322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348355 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 1, 7]
def baseStart_4348355 : Nat := 118140960795 + 4348355 * 2 ^ 59
def prefixEnd_4348355 : Nat := 4983230072969 + 3 ^ 40 * 4348355 * 2
def baseEnd_4348355 : Nat := 744265390460479924921595

theorem tailTrace_4348355 : CollatzResearch.WordTrace tailWord_4348355 prefixEnd_4348355 744265390460479924921595 := by
  unfold tailWord_4348355
  simp only [CollatzResearch.WordTrace]
  refine ⟨158597536161659949754526519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105731690774439966503017679 158597536161659949754526519)
  ·
    refine ⟨237896304242489924631789779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158597536161659949754526519 237896304242489924631789779)
    ·
      refine ⟨356844456363734886947684669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237896304242489924631789779 356844456363734886947684669)
      ·
        refine ⟨133816671136400582605381751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356844456363734886947684669 133816671136400582605381751)
        ·
          refine ⟨200725006704600873908072627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133816671136400582605381751 200725006704600873908072627)
          ·
            refine ⟨301087510056901310862108941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200725006704600873908072627 301087510056901310862108941)
            ·
              refine ⟨112907816271337991573290853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301087510056901310862108941 112907816271337991573290853)
              ·
                refine ⟨21170215550875873419992035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112907816271337991573290853 21170215550875873419992035)
                ·
                  refine ⟨31755323326313810129988053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21170215550875873419992035 31755323326313810129988053)
                  ·
                    refine ⟨744265390460479924921595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31755323326313810129988053 744265390460479924921595)
                    ·
                      rfl

theorem cell23_4348355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 7].length) (baseStart_4348355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348355 prefixEnd_4348355 := by exact prefixLift 4348355
  have htrace : WordTrace (prefixWord ++ tailWord_4348355) baseStart_4348355 baseEnd_4348355 := by
    simpa [prefixWord, tailWord_4348355, baseEnd_4348355] using wordTrace_append hprefix tailTrace_4348355
  have hstable : (prefixWord ++ tailWord_4348355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348355).length < 2 ^ (prefixWord ++ tailWord_4348355).sum := by decide
  have hdescent : baseEnd_4348355 < baseStart_4348355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348409 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 2, 4, 2]
def baseStart_4348409 : Nat := 118140960795 + 4348409 * 2 ^ 59
def prefixEnd_4348409 : Nat := 4983230072969 + 3 ^ 40 * 4348409 * 2
def baseEnd_4348409 : Nat := 2232823899336782563489537

theorem tailTrace_4348409 : CollatzResearch.WordTrace tailWord_4348409 prefixEnd_4348409 2232823899336782563489537 := by
  unfold tailWord_4348409
  simp only [CollatzResearch.WordTrace]
  refine ⟨158599505703464316976992281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105733003802309544651328187 158599505703464316976992281)
  ·
    refine ⟨118949629277598237732744211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158599505703464316976992281 118949629277598237732744211)
    ·
      refine ⟨178424443916397356599116317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118949629277598237732744211 178424443916397356599116317)
      ·
        refine ⟨66909166468649008724668619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178424443916397356599116317 66909166468649008724668619)
        ·
          refine ⟨100363749702973513087002929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66909166468649008724668619 100363749702973513087002929)
          ·
            refine ⟨75272812277230134815252197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100363749702973513087002929 75272812277230134815252197)
            ·
              refine ⟨14113652301980650277859787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75272812277230134815252197 14113652301980650277859787)
              ·
                refine ⟨21170478452970975416789681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14113652301980650277859787 21170478452970975416789681)
                ·
                  refine ⟨15877858839728231562592261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21170478452970975416789681 15877858839728231562592261)
                  ·
                    refine ⟨2977098532449043417986049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15877858839728231562592261 2977098532449043417986049)
                    ·
                      refine ⟨2232823899336782563489537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977098532449043417986049 2232823899336782563489537)
                      ·
                        rfl

theorem cell23_4348409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_4348409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348409 prefixEnd_4348409 := by exact prefixLift 4348409
  have htrace : WordTrace (prefixWord ++ tailWord_4348409) baseStart_4348409 baseEnd_4348409 := by
    simpa [prefixWord, tailWord_4348409, baseEnd_4348409] using wordTrace_append hprefix tailTrace_4348409
  have hstable : (prefixWord ++ tailWord_4348409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348409).length < 2 ^ (prefixWord ++ tailWord_4348409).sum := by decide
  have hdescent : baseEnd_4348409 < baseStart_4348409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348512 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_4348512 : Nat := 118140960795 + 4348512 * 2 ^ 59
def prefixEnd_4348512 : Nat := 4983230072969 + 3 ^ 40 * 4348512 * 2
def baseEnd_4348512 : Nat := 2232876787844195660501563

theorem tailTrace_4348512 : CollatzResearch.WordTrace tailWord_4348512 prefixEnd_4348512 2232876787844195660501563 := by
  unfold tailWord_4348512
  simp only [CollatzResearch.WordTrace]
  refine ⟨79301631211045582783995895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105735508281394110378661193 79301631211045582783995895)
  ·
    refine ⟨118952446816568374175993843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79301631211045582783995895 118952446816568374175993843)
    ·
      refine ⟨178428670224852561263990765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118952446816568374175993843 178428670224852561263990765)
      ·
        refine ⟨66910751334319710473996537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178428670224852561263990765 66910751334319710473996537)
        ·
          refine ⟨50183063500739782855497403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66910751334319710473996537 50183063500739782855497403)
          ·
            refine ⟨75274595251109674283246105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50183063500739782855497403 75274595251109674283246105)
            ·
              refine ⟨56455946438332255712434579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75274595251109674283246105 56455946438332255712434579)
              ·
                refine ⟨84683919657498383568651869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56455946438332255712434579 84683919657498383568651869)
                ·
                  refine ⟨31756469871561893838244451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84683919657498383568651869 31756469871561893838244451)
                  ·
                    refine ⟨47634704807342840757366677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31756469871561893838244451 47634704807342840757366677)
                    ·
                      refine ⟨2232876787844195660501563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47634704807342840757366677 2232876787844195660501563)
                      ·
                        rfl

theorem cell23_4348512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_4348512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348512 prefixEnd_4348512 := by exact prefixLift 4348512
  have htrace : WordTrace (prefixWord ++ tailWord_4348512) baseStart_4348512 baseEnd_4348512 := by
    simpa [prefixWord, tailWord_4348512, baseEnd_4348512] using wordTrace_append hprefix tailTrace_4348512
  have hstable : (prefixWord ++ tailWord_4348512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348512).length < 2 ^ (prefixWord ++ tailWord_4348512).sum := by decide
  have hdescent : baseEnd_4348512 < baseStart_4348512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348526 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_4348526 : Nat := 118140960795 + 4348526 * 2 ^ 59
def prefixEnd_4348526 : Nat := 4983230072969 + 3 ^ 40 * 4348526 * 2
def baseEnd_4348526 : Nat := 744294658857786201908833

theorem tailTrace_4348526 : CollatzResearch.WordTrace tailWord_4348526 prefixEnd_4348526 744294658857786201908833 := by
  unfold tailWord_4348526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19825471630505055744875179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105735848696026963972667621 19825471630505055744875179)
  ·
    refine ⟨29738207445757583617312769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19825471630505055744875179 29738207445757583617312769)
    ·
      refine ⟨22303655584318187712984577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29738207445757583617312769 22303655584318187712984577)
      ·
        refine ⟨16727741688238640784738433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22303655584318187712984577 16727741688238640784738433)
        ·
          refine ⟨12545806266178980588553825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16727741688238640784738433 12545806266178980588553825)
          ·
            refine ⟨9409354699634235441415369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12545806266178980588553825 9409354699634235441415369)
            ·
              refine ⟨7057016024725676581061527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9409354699634235441415369 7057016024725676581061527)
              ·
                refine ⟨10585524037088514871592291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057016024725676581061527 10585524037088514871592291)
                ·
                  refine ⟨15878286055632772307388437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10585524037088514871592291 15878286055632772307388437)
                  ·
                    refine ⟨744294658857786201908833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15878286055632772307388437 744294658857786201908833)
                    ·
                      rfl

theorem cell23_4348526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_4348526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348526 prefixEnd_4348526 := by exact prefixLift 4348526
  have htrace : WordTrace (prefixWord ++ tailWord_4348526) baseStart_4348526 baseEnd_4348526 := by
    simpa [prefixWord, tailWord_4348526, baseEnd_4348526] using wordTrace_append hprefix tailTrace_4348526
  have hstable : (prefixWord ++ tailWord_4348526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348526).length < 2 ^ (prefixWord ++ tailWord_4348526).sum := by decide
  have hdescent : baseEnd_4348526 < baseStart_4348526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348661 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4348661 : Nat := 118140960795 + 4348661 * 2 ^ 59
def prefixEnd_4348661 : Nat := 4983230072969 + 3 ^ 40 * 4348661 * 2
def baseEnd_4348661 : Nat := 2232953296461715577538379

theorem tailTrace_4348661 : CollatzResearch.WordTrace tailWord_4348661 prefixEnd_4348661 2232953296461715577538379 := by
  unfold tailWord_4348661
  simp only [CollatzResearch.WordTrace]
  refine ⟨158608696898551364015165837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105739131265700909343443891 158608696898551364015165837)
  ·
    refine ⟨59478261336956761505687189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158608696898551364015165837 59478261336956761505687189)
    ·
      refine ⟨2788043500169848195579087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59478261336956761505687189 2788043500169848195579087)
      ·
        refine ⟨4182065250254772293368631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788043500169848195579087 4182065250254772293368631)
        ·
          refine ⟨6273097875382158440052947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4182065250254772293368631 6273097875382158440052947)
          ·
            refine ⟨9409646813073237660079421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273097875382158440052947 9409646813073237660079421)
            ·
              refine ⟨3528617554902464122529783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9409646813073237660079421 3528617554902464122529783)
              ·
                refine ⟨5292926332353696183794675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528617554902464122529783 5292926332353696183794675)
                ·
                  refine ⟨7939389498530544275692013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5292926332353696183794675 7939389498530544275692013)
                  ·
                    refine ⟨2977271061948954103384505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7939389498530544275692013 2977271061948954103384505)
                    ·
                      refine ⟨2232953296461715577538379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977271061948954103384505 2232953296461715577538379)
                      ·
                        rfl

theorem cell23_4348661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4348661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348661 prefixEnd_4348661 := by exact prefixLift 4348661
  have htrace : WordTrace (prefixWord ++ tailWord_4348661) baseStart_4348661 baseEnd_4348661 := by
    simpa [prefixWord, tailWord_4348661, baseEnd_4348661] using wordTrace_append hprefix tailTrace_4348661
  have hstable : (prefixWord ++ tailWord_4348661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348661).length < 2 ^ (prefixWord ++ tailWord_4348661).sum := by decide
  have hdescent : baseEnd_4348661 < baseStart_4348661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348669 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4348669 : Nat := 118140960795 + 4348669 * 2 ^ 59
def prefixEnd_4348669 : Nat := 4983230072969 + 3 ^ 40 * 4348669 * 2
def baseEnd_4348669 : Nat := 2232957404306951546238341

theorem tailTrace_4348669 : CollatzResearch.WordTrace tailWord_4348669 prefixEnd_4348669 2232957404306951546238341 := by
  unfold tailWord_4348669
  simp only [CollatzResearch.WordTrace]
  refine ⟨158608988682522381381457061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105739325788348254254304707 158608988682522381381457061)
  ·
    refine ⟨29739185377972946509023199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158608988682522381381457061 29739185377972946509023199)
    ·
      refine ⟨44608778066959419763534799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29739185377972946509023199 44608778066959419763534799)
      ·
        refine ⟨66913167100439129645302199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44608778066959419763534799 66913167100439129645302199)
        ·
          refine ⟨100369750650658694467953299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66913167100439129645302199 100369750650658694467953299)
          ·
            refine ⟨150554625975988041701929949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100369750650658694467953299 150554625975988041701929949)
            ·
              refine ⟨56457984740995515638223731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150554625975988041701929949 56457984740995515638223731)
              ·
                refine ⟨84686977111493273457335597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56457984740995515638223731 84686977111493273457335597)
                ·
                  refine ⟨31757616416809977546500849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84686977111493273457335597 31757616416809977546500849)
                  ·
                    refine ⟨23818212312607483159875637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31757616416809977546500849 23818212312607483159875637)
                    ·
                      refine ⟨2232957404306951546238341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23818212312607483159875637 2232957404306951546238341)
                      ·
                        rfl

theorem cell23_4348669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4348669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348669 prefixEnd_4348669 := by exact prefixLift 4348669
  have htrace : WordTrace (prefixWord ++ tailWord_4348669) baseStart_4348669 baseEnd_4348669 := by
    simpa [prefixWord, tailWord_4348669, baseEnd_4348669] using wordTrace_append hprefix tailTrace_4348669
  have hstable : (prefixWord ++ tailWord_4348669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348669).length < 2 ^ (prefixWord ++ tailWord_4348669).sum := by decide
  have hdescent : baseEnd_4348669 < baseStart_4348669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348676 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_4348676 : Nat := 118140960795 + 4348676 * 2 ^ 59
def prefixEnd_4348676 : Nat := 4983230072969 + 3 ^ 40 * 4348676 * 2
def baseEnd_4348676 : Nat := 744320332890511006283603

theorem tailTrace_4348676 : CollatzResearch.WordTrace tailWord_4348676 prefixEnd_4348676 744320332890511006283603 := by
  unfold tailWord_4348676
  simp only [CollatzResearch.WordTrace]
  refine ⟨79304621996748510788480941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105739495995664681051307921 79304621996748510788480941)
  ·
    refine ⟨29739233248780691545680353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79304621996748510788480941 29739233248780691545680353)
    ·
      refine ⟨22304424936585518659260265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29739233248780691545680353 22304424936585518659260265)
      ·
        refine ⟨16728318702439138994445199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22304424936585518659260265 16728318702439138994445199)
        ·
          refine ⟨25092478053658708491667799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16728318702439138994445199 25092478053658708491667799)
          ·
            refine ⟨37638717080488062737501699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25092478053658708491667799 37638717080488062737501699)
            ·
              refine ⟨56458075620732094106252549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37638717080488062737501699 56458075620732094106252549)
              ·
                refine ⟨10585889178887267644922353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56458075620732094106252549 10585889178887267644922353)
                ·
                  refine ⟨7939416884165450733691765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10585889178887267644922353 7939416884165450733691765)
                  ·
                    refine ⟨744320332890511006283603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7939416884165450733691765 744320332890511006283603)
                    ·
                      rfl

theorem cell23_4348676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_4348676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348676 prefixEnd_4348676 := by exact prefixLift 4348676
  have htrace : WordTrace (prefixWord ++ tailWord_4348676) baseStart_4348676 baseEnd_4348676 := by
    simpa [prefixWord, tailWord_4348676, baseEnd_4348676] using wordTrace_append hprefix tailTrace_4348676
  have hstable : (prefixWord ++ tailWord_4348676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348676).length < 2 ^ (prefixWord ++ tailWord_4348676).sum := by decide
  have hdescent : baseEnd_4348676 < baseStart_4348676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348680 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 5]
def baseStart_4348680 : Nat := 118140960795 + 4348680 * 2 ^ 59
def prefixEnd_4348680 : Nat := 4983230072969 + 3 ^ 40 * 4348680 * 2
def baseEnd_4348680 : Nat := 248107005843794555911199

theorem tailTrace_4348680 : CollatzResearch.WordTrace tailWord_4348680 prefixEnd_4348680 248107005843794555911199 := by
  unfold tailWord_4348680
  simp only [CollatzResearch.WordTrace]
  refine ⟨79304694942741265130053747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105739593256988353506738329 79304694942741265130053747)
  ·
    refine ⟨118957042414111897695080621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79304694942741265130053747 118957042414111897695080621)
    ·
      refine ⟨44608890905291961635655233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118957042414111897695080621 44608890905291961635655233)
      ·
        refine ⟨33456668178968971226741425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44608890905291961635655233 33456668178968971226741425)
        ·
          refine ⟨25092501134226728420056069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33456668178968971226741425 25092501134226728420056069)
          ·
            refine ⟨4704843962667511578760513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25092501134226728420056069 4704843962667511578760513)
            ·
              refine ⟨3528632972000633684070385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4704843962667511578760513 3528632972000633684070385)
              ·
                refine ⟨2646474729000475263052789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3528632972000633684070385 2646474729000475263052789)
                ·
                  refine ⟨248107005843794555911199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646474729000475263052789 248107005843794555911199)
                  ·
                    rfl

theorem cell23_4348680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 5].length) (baseStart_4348680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348680 prefixEnd_4348680 := by exact prefixLift 4348680
  have htrace : WordTrace (prefixWord ++ tailWord_4348680) baseStart_4348680 baseEnd_4348680 := by
    simpa [prefixWord, tailWord_4348680, baseEnd_4348680] using wordTrace_append hprefix tailTrace_4348680
  have hstable : (prefixWord ++ tailWord_4348680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348680).length < 2 ^ (prefixWord ++ tailWord_4348680).sum := by decide
  have hdescent : baseEnd_4348680 < baseStart_4348680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348690 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4348690 : Nat := 118140960795 + 4348690 * 2 ^ 59
def prefixEnd_4348690 : Nat := 4983230072969 + 3 ^ 40 * 4348690 * 2
def baseEnd_4348690 : Nat := 2232968187400695964075745

theorem tailTrace_4348690 : CollatzResearch.WordTrace tailWord_4348690 prefixEnd_4348690 2232968187400695964075745 := by
  unfold tailWord_4348690
  simp only [CollatzResearch.WordTrace]
  refine ⟨39652438653861575491992881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105739836410297534645314349 39652438653861575491992881)
  ·
    refine ⟨29739328990396181618994661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39652438653861575491992881 29739328990396181618994661)
    ·
      refine ⟨5576124185699284053561499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29739328990396181618994661 5576124185699284053561499)
      ·
        refine ⟨8364186278548926080342249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5576124185699284053561499 8364186278548926080342249)
        ·
          refine ⟨6273139708911694560256687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8364186278548926080342249 6273139708911694560256687)
          ·
            refine ⟨9409709563367541840385031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273139708911694560256687 9409709563367541840385031)
            ·
              refine ⟨14114564345051312760577547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9409709563367541840385031 14114564345051312760577547)
              ·
                refine ⟨21171846517576969140866321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14114564345051312760577547 21171846517576969140866321)
                ·
                  refine ⟨15878884888182726855649741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21171846517576969140866321 15878884888182726855649741)
                  ·
                    refine ⟨5954581833068522570868653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15878884888182726855649741 5954581833068522570868653)
                    ·
                      refine ⟨2232968187400695964075745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5954581833068522570868653 2232968187400695964075745)
                      ·
                        rfl

theorem cell23_4348690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4348690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348690 prefixEnd_4348690 := by exact prefixLift 4348690
  have htrace : WordTrace (prefixWord ++ tailWord_4348690) baseStart_4348690 baseEnd_4348690 := by
    simpa [prefixWord, tailWord_4348690, baseEnd_4348690] using wordTrace_append hprefix tailTrace_4348690
  have hstable : (prefixWord ++ tailWord_4348690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348690).length < 2 ^ (prefixWord ++ tailWord_4348690).sum := by decide
  have hdescent : baseEnd_4348690 < baseStart_4348690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348716 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_4348716 : Nat := 118140960795 + 4348716 * 2 ^ 59
def prefixEnd_4348716 : Nat := 4983230072969 + 3 ^ 40 * 4348716 * 2
def baseEnd_4348716 : Nat := 2232981537897712862350625

theorem tailTrace_4348716 : CollatzResearch.WordTrace tailWord_4348716 prefixEnd_4348716 2232981537897712862350625 := by
  unfold tailWord_4348716
  simp only [CollatzResearch.WordTrace]
  refine ⟨79305351456676054204209001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105740468608901405605612001 79305351456676054204209001)
  ·
    refine ⟨59479013592507040653156751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79305351456676054204209001 59479013592507040653156751)
    ·
      refine ⟨89218520388760560979735127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59479013592507040653156751 89218520388760560979735127)
      ·
        refine ⟨133827780583140841469602691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89218520388760560979735127 133827780583140841469602691)
        ·
          refine ⟨200741670874711262204404037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133827780583140841469602691 200741670874711262204404037)
          ·
            refine ⟨37639063289008361663325757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200741670874711262204404037 37639063289008361663325757)
            ·
              refine ⟨14114648733378135623747159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37639063289008361663325757 14114648733378135623747159)
              ·
                refine ⟨21171973100067203435620739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14114648733378135623747159 21171973100067203435620739)
                ·
                  refine ⟨31757959650100805153431109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21171973100067203435620739 31757959650100805153431109)
                  ·
                    refine ⟨5954617434393900966268333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31757959650100805153431109 5954617434393900966268333)
                    ·
                      refine ⟨2232981537897712862350625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5954617434393900966268333 2232981537897712862350625)
                      ·
                        rfl

theorem cell23_4348716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_4348716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348716 prefixEnd_4348716 := by exact prefixLift 4348716
  have htrace : WordTrace (prefixWord ++ tailWord_4348716) baseStart_4348716 baseEnd_4348716 := by
    simpa [prefixWord, tailWord_4348716, baseEnd_4348716] using wordTrace_append hprefix tailTrace_4348716
  have hstable : (prefixWord ++ tailWord_4348716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348716).length < 2 ^ (prefixWord ++ tailWord_4348716).sum := by decide
  have hdescent : baseEnd_4348716 < baseStart_4348716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348739 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_4348739 : Nat := 118140960795 + 4348739 * 2 ^ 59
def prefixEnd_4348739 : Nat := 4983230072969 + 3 ^ 40 * 4348739 * 2
def baseEnd_4348739 : Nat := 2232993347952766272363019

theorem tailTrace_4348739 : CollatzResearch.WordTrace tailWord_4348739 prefixEnd_4348739 2232993347952766272363019 := by
  unfold tailWord_4348739
  simp only [CollatzResearch.WordTrace]
  refine ⟨158611541792268783336505271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105741027861512522224336847 158611541792268783336505271)
  ·
    refine ⟨237917312688403175004757907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158611541792268783336505271 237917312688403175004757907)
    ·
      refine ⟨356875969032604762507136861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237917312688403175004757907 356875969032604762507136861)
      ·
        refine ⟨133828488387226785940176323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 356875969032604762507136861 133828488387226785940176323)
        ·
          refine ⟨200742732580840178910264485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133828488387226785940176323 200742732580840178910264485)
          ·
            refine ⟨37639262358907533545674591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200742732580840178910264485 37639262358907533545674591)
            ·
              refine ⟨56458893538361300318511887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37639262358907533545674591 56458893538361300318511887)
              ·
                refine ⟨84688340307541950477767831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56458893538361300318511887 84688340307541950477767831)
                ·
                  refine ⟨127032510461312925716651747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84688340307541950477767831 127032510461312925716651747)
                  ·
                    refine ⟨190548765691969388574977621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127032510461312925716651747 190548765691969388574977621)
                    ·
                      refine ⟨2232993347952766272363019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 190548765691969388574977621 2232993347952766272363019)
                      ·
                        rfl

theorem cell23_4348739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_4348739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348739 prefixEnd_4348739 := by exact prefixLift 4348739
  have htrace : WordTrace (prefixWord ++ tailWord_4348739) baseStart_4348739 baseEnd_4348739 := by
    simpa [prefixWord, tailWord_4348739, baseEnd_4348739] using wordTrace_append hprefix tailTrace_4348739
  have hstable : (prefixWord ++ tailWord_4348739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348739).length < 2 ^ (prefixWord ++ tailWord_4348739).sum := by decide
  have hdescent : baseEnd_4348739 < baseStart_4348739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348773 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 1, 5, 2]
def baseStart_4348773 : Nat := 118140960795 + 4348773 * 2 ^ 59
def prefixEnd_4348773 : Nat := 4983230072969 + 3 ^ 40 * 4348773 * 2
def baseEnd_4348773 : Nat := 2233010806295019139337863

theorem tailTrace_4348773 : CollatzResearch.WordTrace tailWord_4348773 prefixEnd_4348773 2233010806295019139337863 := by
  unfold tailWord_4348773
  simp only [CollatzResearch.WordTrace]
  refine ⟨158612781874145607143242973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105741854582763738095495315 158612781874145607143242973)
  ·
    refine ⟨59479793202804602678716115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158612781874145607143242973 59479793202804602678716115)
    ·
      refine ⟨89219689804206904018074173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59479793202804602678716115 89219689804206904018074173)
      ·
        refine ⟨33457383676577589006777815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89219689804206904018074173 33457383676577589006777815)
        ·
          refine ⟨50186075514866383510166723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33457383676577589006777815 50186075514866383510166723)
          ·
            refine ⟨75279113272299575265250085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50186075514866383510166723 75279113272299575265250085)
            ·
              refine ⟨14114833738556170362234391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75279113272299575265250085 14114833738556170362234391)
              ·
                refine ⟨21172250607834255543351587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14114833738556170362234391 21172250607834255543351587)
                ·
                  refine ⟨31758375911751383315027381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21172250607834255543351587 31758375911751383315027381)
                  ·
                    refine ⟨2977347741726692185783817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31758375911751383315027381 2977347741726692185783817)
                    ·
                      refine ⟨2233010806295019139337863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977347741726692185783817 2233010806295019139337863)
                      ·
                        rfl

theorem cell23_4348773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_4348773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348773 prefixEnd_4348773 := by exact prefixLift 4348773
  have htrace : WordTrace (prefixWord ++ tailWord_4348773) baseStart_4348773 baseEnd_4348773 := by
    simpa [prefixWord, tailWord_4348773, baseEnd_4348773] using wordTrace_append hprefix tailTrace_4348773
  have hstable : (prefixWord ++ tailWord_4348773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348773).length < 2 ^ (prefixWord ++ tailWord_4348773).sum := by decide
  have hdescent : baseEnd_4348773 < baseStart_4348773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348823 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_4348823 : Nat := 118140960795 + 4348823 * 2 ^ 59
def prefixEnd_4348823 : Nat := 4983230072969 + 3 ^ 40 * 4348823 * 2
def baseEnd_4348823 : Nat := 2233036480327743943712633

theorem tailTrace_4348823 : CollatzResearch.WordTrace tailWord_4348823 prefixEnd_4348823 2233036480327743943712633 := by
  unfold tailWord_4348823
  simp only [CollatzResearch.WordTrace]
  refine ⟨158614605523964465682563123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105743070349309643788375415 158614605523964465682563123)
  ·
    refine ⟨237921908285946698523844685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158614605523964465682563123 237921908285946698523844685)
    ·
      refine ⟨89220715607230011946441757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237921908285946698523844685 89220715607230011946441757)
      ·
        refine ⟨33457768352711254479915659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89220715607230011946441757 33457768352711254479915659)
        ·
          refine ⟨50186652529066881719873489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33457768352711254479915659 50186652529066881719873489)
          ·
            refine ⟨37639989396800161289905117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50186652529066881719873489 37639989396800161289905117)
            ·
              refine ⟨14114996023800060483714419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37639989396800161289905117 14114996023800060483714419)
              ·
                refine ⟨21172494035700090725571629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14114996023800060483714419 21172494035700090725571629)
                ·
                  refine ⟨7939685263387534022089361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21172494035700090725571629 7939685263387534022089361)
                  ·
                    refine ⟨5954763947540650516567021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7939685263387534022089361 5954763947540650516567021)
                    ·
                      refine ⟨2233036480327743943712633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5954763947540650516567021 2233036480327743943712633)
                      ·
                        rfl

theorem cell23_4348823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_4348823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348823 prefixEnd_4348823 := by exact prefixLift 4348823
  have htrace : WordTrace (prefixWord ++ tailWord_4348823) baseStart_4348823 baseEnd_4348823 := by
    simpa [prefixWord, tailWord_4348823, baseEnd_4348823] using wordTrace_append hprefix tailTrace_4348823
  have hstable : (prefixWord ++ tailWord_4348823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348823).length < 2 ^ (prefixWord ++ tailWord_4348823).sum := by decide
  have hdescent : baseEnd_4348823 < baseStart_4348823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348833 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4348833 : Nat := 118140960795 + 4348833 * 2 ^ 59
def prefixEnd_4348833 : Nat := 4983230072969 + 3 ^ 40 * 4348833 * 2
def baseEnd_4348833 : Nat := 2233041615134288904587587

theorem tailTrace_4348833 : CollatzResearch.WordTrace tailWord_4348833 prefixEnd_4348833 2233041615134288904587587 := by
  unfold tailWord_4348833
  simp only [CollatzResearch.WordTrace]
  refine ⟨158614970253928237390427153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105743313502618824926951435 158614970253928237390427153)
  ·
    refine ⟨118961227690446178042820365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158614970253928237390427153 118961227690446178042820365)
    ·
      refine ⟨44610460383917316766057637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118961227690446178042820365 44610460383917316766057637)
      ·
        refine ⟨8364461321984496893635807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44610460383917316766057637 8364461321984496893635807)
        ·
          refine ⟨12546691982976745340453711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8364461321984496893635807 12546691982976745340453711)
          ·
            refine ⟨18820037974465118010680567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12546691982976745340453711 18820037974465118010680567)
            ·
              refine ⟨28230056961697677016020851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18820037974465118010680567 28230056961697677016020851)
              ·
                refine ⟨42345085442546515524031277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28230056961697677016020851 42345085442546515524031277)
                ·
                  refine ⟨15879407040954943321511729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42345085442546515524031277 15879407040954943321511729)
                  ·
                    refine ⟨11909555280716207491133797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15879407040954943321511729 11909555280716207491133797)
                    ·
                      refine ⟨2233041615134288904587587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11909555280716207491133797 2233041615134288904587587)
                      ·
                        rfl

theorem cell23_4348833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4348833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348833 prefixEnd_4348833 := by exact prefixLift 4348833
  have htrace : WordTrace (prefixWord ++ tailWord_4348833) baseStart_4348833 baseEnd_4348833 := by
    simpa [prefixWord, tailWord_4348833, baseEnd_4348833] using wordTrace_append hprefix tailTrace_4348833
  have hstable : (prefixWord ++ tailWord_4348833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348833).length < 2 ^ (prefixWord ++ tailWord_4348833).sum := by decide
  have hdescent : baseEnd_4348833 < baseStart_4348833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348853 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_4348853 : Nat := 118140960795 + 4348853 * 2 ^ 59
def prefixEnd_4348853 : Nat := 4983230072969 + 3 ^ 40 * 4348853 * 2
def baseEnd_4348853 : Nat := 2233051884747378826337495

theorem tailTrace_4348853 : CollatzResearch.WordTrace tailWord_4348853 prefixEnd_4348853 2233051884747378826337495 := by
  unfold tailWord_4348853
  simp only [CollatzResearch.WordTrace]
  refine ⟨158615699713855780806155213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105743799809237187204103475 158615699713855780806155213)
  ·
    refine ⟨59480887392695917802308205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158615699713855780806155213 59480887392695917802308205)
    ·
      refine ⟨22305332772260969175865577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59480887392695917802308205 22305332772260969175865577)
      ·
        refine ⟨16728999579195726881899183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22305332772260969175865577 16728999579195726881899183)
        ·
          refine ⟨25093499368793590322848775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16728999579195726881899183 25093499368793590322848775)
          ·
            refine ⟨37640249053190385484273163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25093499368793590322848775 37640249053190385484273163)
            ·
              refine ⟨56460373579785578226409745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37640249053190385484273163 56460373579785578226409745)
              ·
                refine ⟨42345280184839183669807309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56460373579785578226409745 42345280184839183669807309)
                ·
                  refine ⟨15879480069314693876177741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42345280184839183669807309 15879480069314693876177741)
                  ·
                    refine ⟨5954805025993010203566653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15879480069314693876177741 5954805025993010203566653)
                    ·
                      refine ⟨2233051884747378826337495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5954805025993010203566653 2233051884747378826337495)
                      ·
                        rfl

theorem cell23_4348853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_4348853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348853 prefixEnd_4348853 := by exact prefixLift 4348853
  have htrace : WordTrace (prefixWord ++ tailWord_4348853) baseStart_4348853 baseEnd_4348853 := by
    simpa [prefixWord, tailWord_4348853, baseEnd_4348853] using wordTrace_append hprefix tailTrace_4348853
  have hstable : (prefixWord ++ tailWord_4348853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348853).length < 2 ^ (prefixWord ++ tailWord_4348853).sum := by decide
  have hdescent : baseEnd_4348853 < baseStart_4348853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348856 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_4348856 : Nat := 118140960795 + 4348856 * 2 ^ 59
def prefixEnd_4348856 : Nat := 4983230072969 + 3 ^ 40 * 4348856 * 2
def baseEnd_4348856 : Nat := 744351141729780771533327

theorem tailTrace_4348856 : CollatzResearch.WordTrace tailWord_4348856 prefixEnd_4348856 744351141729780771533327 := by
  unfold tailWord_4348856
  simp only [CollatzResearch.WordTrace]
  refine ⟨79307904566422456159257211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105743872755229941545676281 79307904566422456159257211)
  ·
    refine ⟨118961856849633684238885817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79307904566422456159257211 118961856849633684238885817)
    ·
      refine ⟨89221392637225263179164363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118961856849633684238885817 89221392637225263179164363)
      ·
        refine ⟨133832088955837894768746545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89221392637225263179164363 133832088955837894768746545)
        ·
          refine ⟨100374066716878421076559909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133832088955837894768746545 100374066716878421076559909)
          ·
            refine ⟨18820137509414703951854983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100374066716878421076559909 18820137509414703951854983)
            ·
              refine ⟨28230206264122055927782475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18820137509414703951854983 28230206264122055927782475)
              ·
                refine ⟨42345309396183083891673713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28230206264122055927782475 42345309396183083891673713)
                ·
                  refine ⟨31758982047137312918755285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42345309396183083891673713 31758982047137312918755285)
                  ·
                    refine ⟨744351141729780771533327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31758982047137312918755285 744351141729780771533327)
                    ·
                      rfl

theorem cell23_4348856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_4348856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348856 prefixEnd_4348856 := by exact prefixLift 4348856
  have htrace : WordTrace (prefixWord ++ tailWord_4348856) baseStart_4348856 baseEnd_4348856 := by
    simpa [prefixWord, tailWord_4348856, baseEnd_4348856] using wordTrace_append hprefix tailTrace_4348856
  have hstable : (prefixWord ++ tailWord_4348856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348856).length < 2 ^ (prefixWord ++ tailWord_4348856).sum := by decide
  have hdescent : baseEnd_4348856 < baseStart_4348856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348880 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 1, 3, 2]
def baseStart_4348880 : Nat := 118140960795 + 4348880 * 2 ^ 59
def prefixEnd_4348880 : Nat := 4983230072969 + 3 ^ 40 * 4348880 * 2
def baseEnd_4348880 : Nat := 2233065748725050220699871

theorem tailTrace_4348880 : CollatzResearch.WordTrace tailWord_4348880 prefixEnd_4348880 2233065748725050220699871 := by
  unfold tailWord_4348880
  simp only [CollatzResearch.WordTrace]
  refine ⟨79308342242378982208694047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105744456323171976278258729 79308342242378982208694047)
  ·
    refine ⟨118962513363568473313041071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79308342242378982208694047 118962513363568473313041071)
    ·
      refine ⟨178443770045352709969561607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118962513363568473313041071 178443770045352709969561607)
      ·
        refine ⟨267665655068029064954342411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178443770045352709969561607 267665655068029064954342411)
        ·
          refine ⟨401498482602043597431513617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267665655068029064954342411 401498482602043597431513617)
          ·
            refine ⟨301123861951532698073635213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401498482602043597431513617 301123861951532698073635213)
            ·
              refine ⟨112921448231824761777613205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301123861951532698073635213 112921448231824761777613205)
              ·
                refine ⟨5293192885866785708325619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112921448231824761777613205 5293192885866785708325619)
                ·
                  refine ⟨7939789328800178562488429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5293192885866785708325619 7939789328800178562488429)
                  ·
                    refine ⟨2977420998300066960933161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7939789328800178562488429 2977420998300066960933161)
                    ·
                      refine ⟨2233065748725050220699871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977420998300066960933161 2233065748725050220699871)
                      ·
                        rfl

theorem cell23_4348880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 3, 2].length) (baseStart_4348880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348880 prefixEnd_4348880 := by exact prefixLift 4348880
  have htrace : WordTrace (prefixWord ++ tailWord_4348880) baseStart_4348880 baseEnd_4348880 := by
    simpa [prefixWord, tailWord_4348880, baseEnd_4348880] using wordTrace_append hprefix tailTrace_4348880
  have hstable : (prefixWord ++ tailWord_4348880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348880).length < 2 ^ (prefixWord ++ tailWord_4348880).sum := by decide
  have hdescent : baseEnd_4348880 < baseStart_4348880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348903 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 2, 6]
def baseStart_4348903 : Nat := 118140960795 + 4348903 * 2 ^ 59
def prefixEnd_4348903 : Nat := 4983230072969 + 3 ^ 40 * 4348903 * 2
def baseEnd_4348903 : Nat := 744359186260034543570755

theorem tailTrace_4348903 : CollatzResearch.WordTrace tailWord_4348903 prefixEnd_4348903 744359186260034543570755 := by
  unfold tailWord_4348903
  simp only [CollatzResearch.WordTrace]
  refine ⟨158617523363674639345475363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105745015575783092896983575 158617523363674639345475363)
  ·
    refine ⟨237926285045511959018213045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158617523363674639345475363 237926285045511959018213045)
    ·
      refine ⟨22305589223016746157957473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 237926285045511959018213045 22305589223016746157957473)
      ·
        refine ⟨16729191917262559618468105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22305589223016746157957473 16729191917262559618468105)
        ·
          refine ⟨12546893937946919713851079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16729191917262559618468105 12546893937946919713851079)
          ·
            refine ⟨18820340906920379570776619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12546893937946919713851079 18820340906920379570776619)
            ·
              refine ⟨28230511360380569356164929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18820340906920379570776619 28230511360380569356164929)
              ·
                refine ⟨21172883520285427017123697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28230511360380569356164929 21172883520285427017123697)
                ·
                  refine ⟨15879662640214070262842773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21172883520285427017123697 15879662640214070262842773)
                  ·
                    refine ⟨744359186260034543570755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15879662640214070262842773 744359186260034543570755)
                    ·
                      rfl

theorem cell23_4348903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_4348903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348903 prefixEnd_4348903 := by exact prefixLift 4348903
  have htrace : WordTrace (prefixWord ++ tailWord_4348903) baseStart_4348903 baseEnd_4348903 := by
    simpa [prefixWord, tailWord_4348903, baseEnd_4348903] using wordTrace_append hprefix tailTrace_4348903
  have hstable : (prefixWord ++ tailWord_4348903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348903).length < 2 ^ (prefixWord ++ tailWord_4348903).sum := by decide
  have hdescent : baseEnd_4348903 < baseStart_4348903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348963 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 4, 5]
def baseStart_4348963 : Nat := 118140960795 + 4348963 * 2 ^ 59
def prefixEnd_4348963 : Nat := 4983230072969 + 3 ^ 40 * 4348963 * 2
def baseEnd_4348963 : Nat := 744369455873124465320663

theorem tailTrace_4348963 : CollatzResearch.WordTrace tailWord_4348963 prefixEnd_4348963 744369455873124465320663 := by
  unfold tailWord_4348963
  simp only [CollatzResearch.WordTrace]
  refine ⟨158619711743457269592659543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105746474495638179728439695 158619711743457269592659543)
  ·
    refine ⟨237929567615185904388989315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158619711743457269592659543 237929567615185904388989315)
    ·
      refine ⟨356894351422778856583483973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237929567615185904388989315 356894351422778856583483973)
      ·
        refine ⟨66917690891771035609403245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 356894351422778856583483973 66917690891771035609403245)
        ·
          refine ⟨25094134084414138353526217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66917690891771035609403245 25094134084414138353526217)
          ·
            refine ⟨18820600563310603765144663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25094134084414138353526217 18820600563310603765144663)
            ·
              refine ⟨28230900844965905647716995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18820600563310603765144663 28230900844965905647716995)
              ·
                refine ⟨42346351267448858471575493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28230900844965905647716995 42346351267448858471575493)
                ·
                  refine ⟨7939940862646660963420405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42346351267448858471575493 7939940862646660963420405)
                  ·
                    refine ⟨744369455873124465320663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7939940862646660963420405 744369455873124465320663)
                    ·
                      rfl

theorem cell23_4348963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 5].length) (baseStart_4348963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348963 prefixEnd_4348963 := by exact prefixLift 4348963
  have htrace : WordTrace (prefixWord ++ tailWord_4348963) baseStart_4348963 baseEnd_4348963 := by
    simpa [prefixWord, tailWord_4348963, baseEnd_4348963] using wordTrace_append hprefix tailTrace_4348963
  have hstable : (prefixWord ++ tailWord_4348963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348963).length < 2 ^ (prefixWord ++ tailWord_4348963).sum := by decide
  have hdescent : baseEnd_4348963 < baseStart_4348963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348967 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 7]
def baseStart_4348967 : Nat := 118140960795 + 4348967 * 2 ^ 59
def prefixEnd_4348967 : Nat := 4983230072969 + 3 ^ 40 * 4348967 * 2
def baseEnd_4348967 : Nat := 248123380171332375590219

theorem tailTrace_4348967 : CollatzResearch.WordTrace tailWord_4348967 prefixEnd_4348967 248123380171332375590219 := by
  unfold tailWord_4348967
  simp only [CollatzResearch.WordTrace]
  refine ⟨158619857635442778275805155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105746571756961852183870103 158619857635442778275805155)
  ·
    refine ⟨237929786453164167413707733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158619857635442778275805155 237929786453164167413707733)
    ·
      refine ⟨5576479369996035173758775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 237929786453164167413707733 5576479369996035173758775)
      ·
        refine ⟨8364719054994052760638163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5576479369996035173758775 8364719054994052760638163)
        ·
          refine ⟨12547078582491079140957245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8364719054994052760638163 12547078582491079140957245)
          ·
            refine ⟨4705154468434154677858967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12547078582491079140957245 4705154468434154677858967)
            ·
              refine ⟨7057731702651232016788451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705154468434154677858967 7057731702651232016788451)
              ·
                refine ⟨10586597553976848025182677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057731702651232016788451 10586597553976848025182677)
                ·
                  refine ⟨248123380171332375590219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10586597553976848025182677 248123380171332375590219)
                  ·
                    rfl

theorem cell23_4348967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 7].length) (baseStart_4348967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348967 prefixEnd_4348967 := by exact prefixLift 4348967
  have htrace : WordTrace (prefixWord ++ tailWord_4348967) baseStart_4348967 baseEnd_4348967 := by
    simpa [prefixWord, tailWord_4348967, baseEnd_4348967] using wordTrace_append hprefix tailTrace_4348967
  have hstable : (prefixWord ++ tailWord_4348967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348967).length < 2 ^ (prefixWord ++ tailWord_4348967).sum := by decide
  have hdescent : baseEnd_4348967 < baseStart_4348967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4348983 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_4348983 : Nat := 118140960795 + 4348983 * 2 ^ 59
def prefixEnd_4348983 : Nat := 4983230072969 + 3 ^ 40 * 4348983 * 2
def baseEnd_4348983 : Nat := 2233118637232463317711897

theorem tailTrace_4348983 : CollatzResearch.WordTrace tailWord_4348983 prefixEnd_4348983 2233118637232463317711897 := by
  unfold tailWord_4348983
  simp only [CollatzResearch.WordTrace]
  refine ⟨158620441203384813008387603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105746960802256542005591735 158620441203384813008387603)
  ·
    refine ⟨237930661805077219512581405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158620441203384813008387603 237930661805077219512581405)
    ·
      refine ⟨89223998176903957317218027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237930661805077219512581405 89223998176903957317218027)
      ·
        refine ⟨133835997265355935975827041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89223998176903957317218027 133835997265355935975827041)
        ·
          refine ⟨100376997949016951981870281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133835997265355935975827041 100376997949016951981870281)
          ·
            refine ⟨75282748461762713986402711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100376997949016951981870281 75282748461762713986402711)
            ·
              refine ⟨112924122692644070979604067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75282748461762713986402711 112924122692644070979604067)
              ·
                refine ⟨169386184038966106469406101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112924122692644070979604067 169386184038966106469406101)
                ·
                  refine ⟨7939977376826536240753411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169386184038966106469406101 7939977376826536240753411)
                  ·
                    refine ⟨11909966065239804361130117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7939977376826536240753411 11909966065239804361130117)
                    ·
                      refine ⟨2233118637232463317711897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11909966065239804361130117 2233118637232463317711897)
                      ·
                        rfl

theorem cell23_4348983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_4348983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4348983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4348983 prefixEnd_4348983 := by exact prefixLift 4348983
  have htrace : WordTrace (prefixWord ++ tailWord_4348983) baseStart_4348983 baseEnd_4348983 := by
    simpa [prefixWord, tailWord_4348983, baseEnd_4348983] using wordTrace_append hprefix tailTrace_4348983
  have hstable : (prefixWord ++ tailWord_4348983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4348983).length < 2 ^ (prefixWord ++ tailWord_4348983).sum := by decide
  have hdescent : baseEnd_4348983 < baseStart_4348983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4348983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349000 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_4349000 : Nat := 118140960795 + 4349000 * 2 ^ 59
def prefixEnd_4349000 : Nat := 4983230072969 + 3 ^ 40 * 4349000 * 2
def baseEnd_4349000 : Nat := 2233127366403589751199319

theorem tailTrace_4349000 : CollatzResearch.WordTrace tailWord_4349000 prefixEnd_4349000 2233127366403589751199319 := by
  unfold tailWord_4349000
  simp only [CollatzResearch.WordTrace]
  refine ⟨79310530622161612455878227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105747374162882149941170969 79310530622161612455878227)
  ·
    refine ⟨118965795933242418683817341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79310530622161612455878227 118965795933242418683817341)
    ·
      refine ⟨44612173474965907006431503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118965795933242418683817341 44612173474965907006431503)
      ·
        refine ⟨66918260212448860509647255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44612173474965907006431503 66918260212448860509647255)
        ·
          refine ⟨100377390318673290764470883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66918260212448860509647255 100377390318673290764470883)
          ·
            refine ⟨150566085478009936146706325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100377390318673290764470883 150566085478009936146706325)
            ·
              refine ⟨7057785256781715756876859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150566085478009936146706325 7057785256781715756876859)
              ·
                refine ⟨10586677885172573635315289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057785256781715756876859 10586677885172573635315289)
                ·
                  refine ⟨7940008413879430226486467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10586677885172573635315289 7940008413879430226486467)
                  ·
                    refine ⟨11910012620819145339729701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7940008413879430226486467 11910012620819145339729701)
                    ·
                      refine ⟨2233127366403589751199319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11910012620819145339729701 2233127366403589751199319)
                      ·
                        rfl

theorem cell23_4349000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_4349000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349000 prefixEnd_4349000 := by exact prefixLift 4349000
  have htrace : WordTrace (prefixWord ++ tailWord_4349000) baseStart_4349000 baseEnd_4349000 := by
    simpa [prefixWord, tailWord_4349000, baseEnd_4349000] using wordTrace_append hprefix tailTrace_4349000
  have hstable : (prefixWord ++ tailWord_4349000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349000).length < 2 ^ (prefixWord ++ tailWord_4349000).sum := by decide
  have hdescent : baseEnd_4349000 < baseStart_4349000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349013 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4349013 : Nat := 118140960795 + 4349013 * 2 ^ 59
def prefixEnd_4349013 : Nat := 4983230072969 + 3 ^ 40 * 4349013 * 2
def baseEnd_4349013 : Nat := 2233134041652098200336759

theorem tailTrace_4349013 : CollatzResearch.WordTrace tailWord_4349013 prefixEnd_4349013 2233134041652098200336759 := by
  unfold tailWord_4349013
  simp only [CollatzResearch.WordTrace]
  refine ⟨158621535393276128131979693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105747690262184085421319795 158621535393276128131979693)
  ·
    refine ⟨59483075772478548049492385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158621535393276128131979693 59483075772478548049492385)
    ·
      refine ⟨44612306829358911037119289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59483075772478548049492385 44612306829358911037119289)
      ·
        refine ⟨33459230122019183277839467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44612306829358911037119289 33459230122019183277839467)
        ·
          refine ⟨50188845183028774916759201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33459230122019183277839467 50188845183028774916759201)
          ·
            refine ⟨37641633887271581187569401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50188845183028774916759201 37641633887271581187569401)
            ·
              refine ⟨28231225415453685890677051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37641633887271581187569401 28231225415453685890677051)
              ·
                refine ⟨42346838123180528836015577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28231225415453685890677051 42346838123180528836015577)
                ·
                  refine ⟨31760128592385396627011683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42346838123180528836015577 31760128592385396627011683)
                  ·
                    refine ⟨47640192888578094940517525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31760128592385396627011683 47640192888578094940517525)
                    ·
                      refine ⟨2233134041652098200336759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47640192888578094940517525 2233134041652098200336759)
                      ·
                        rfl

theorem cell23_4349013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4349013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349013 prefixEnd_4349013 := by exact prefixLift 4349013
  have htrace : WordTrace (prefixWord ++ tailWord_4349013) baseStart_4349013 baseEnd_4349013 := by
    simpa [prefixWord, tailWord_4349013, baseEnd_4349013] using wordTrace_append hprefix tailTrace_4349013
  have hstable : (prefixWord ++ tailWord_4349013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349013).length < 2 ^ (prefixWord ++ tailWord_4349013).sum := by decide
  have hdescent : baseEnd_4349013 < baseStart_4349013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349063 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4349063 : Nat := 118140960795 + 4349063 * 2 ^ 59
def prefixEnd_4349063 : Nat := 4983230072969 + 3 ^ 40 * 4349063 * 2
def baseEnd_4349063 : Nat := 2233159715684823004711529

theorem tailTrace_4349063 : CollatzResearch.WordTrace tailWord_4349063 prefixEnd_4349063 2233159715684823004711529 := by
  unfold tailWord_4349063
  simp only [CollatzResearch.WordTrace]
  refine ⟨158623359043094986671299843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105748906028729991114199895 158623359043094986671299843)
  ·
    refine ⟨237935038564642480006949765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158623359043094986671299843 237935038564642480006949765)
    ·
      refine ⟨44612819730870465001303081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 237935038564642480006949765 44612819730870465001303081)
      ·
        refine ⟨33459614798152848750977311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44612819730870465001303081 33459614798152848750977311)
        ·
          refine ⟨50189422197229273126465967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33459614798152848750977311 50189422197229273126465967)
          ·
            refine ⟨75284133295843909689698951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50189422197229273126465967 75284133295843909689698951)
            ·
              refine ⟨112926199943765864534548427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75284133295843909689698951 112926199943765864534548427)
              ·
                refine ⟨169389299915648796801822641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112926199943765864534548427 169389299915648796801822641)
                ·
                  refine ⟨127041974936736597601366981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169389299915648796801822641 127041974936736597601366981)
                  ·
                    refine ⟨23820370300638112050256309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127041974936736597601366981 23820370300638112050256309)
                    ·
                      refine ⟨2233159715684823004711529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23820370300638112050256309 2233159715684823004711529)
                      ·
                        rfl

theorem cell23_4349063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4349063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349063 prefixEnd_4349063 := by exact prefixLift 4349063
  have htrace : WordTrace (prefixWord ++ tailWord_4349063) baseStart_4349063 baseEnd_4349063 := by
    simpa [prefixWord, tailWord_4349063, baseEnd_4349063] using wordTrace_append hprefix tailTrace_4349063
  have hstable : (prefixWord ++ tailWord_4349063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349063).length < 2 ^ (prefixWord ++ tailWord_4349063).sum := by decide
  have hdescent : baseEnd_4349063 < baseStart_4349063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349084 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4349084 : Nat := 118140960795 + 4349084 * 2 ^ 59
def prefixEnd_4349084 : Nat := 4983230072969 + 3 ^ 40 * 4349084 * 2
def baseEnd_4349084 : Nat := 2233170498778567422548933

theorem tailTrace_4349084 : CollatzResearch.WordTrace tailWord_4349084 prefixEnd_4349084 2233170498778567422548933 := by
  unfold tailWord_4349084
  simp only [CollatzResearch.WordTrace]
  refine ⟨79312062488009453628907153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105749416650679271505209537 79312062488009453628907153)
  ·
    refine ⟨59484046866007090221680365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79312062488009453628907153 59484046866007090221680365)
    ·
      refine ⟨22306517574752658833130137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59484046866007090221680365 22306517574752658833130137)
      ·
        refine ⟨16729888181064494124847603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22306517574752658833130137 16729888181064494124847603)
        ·
          refine ⟨25094832271596741187271405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16729888181064494124847603 25094832271596741187271405)
          ·
            refine ⟨9410562101848777945226777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25094832271596741187271405 9410562101848777945226777)
            ·
              refine ⟨7057921576386583458920083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9410562101848777945226777 7057921576386583458920083)
              ·
                refine ⟨10586882364579875188380125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057921576386583458920083 10586882364579875188380125)
                ·
                  refine ⟨3970080886717453195642547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10586882364579875188380125 3970080886717453195642547)
                  ·
                    refine ⟨5955121330076179793463821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970080886717453195642547 5955121330076179793463821)
                    ·
                      refine ⟨2233170498778567422548933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955121330076179793463821 2233170498778567422548933)
                      ·
                        rfl

theorem cell23_4349084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4349084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349084 prefixEnd_4349084 := by exact prefixLift 4349084
  have htrace : WordTrace (prefixWord ++ tailWord_4349084) baseStart_4349084 baseEnd_4349084 := by
    simpa [prefixWord, tailWord_4349084, baseEnd_4349084] using wordTrace_append hprefix tailTrace_4349084
  have hstable : (prefixWord ++ tailWord_4349084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349084).length < 2 ^ (prefixWord ++ tailWord_4349084).sum := by decide
  have hdescent : baseEnd_4349084 < baseStart_4349084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349118 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_4349118 : Nat := 118140960795 + 4349118 * 2 ^ 59
def prefixEnd_4349118 : Nat := 4983230072969 + 3 ^ 40 * 4349118 * 2
def baseEnd_4349118 : Nat := 2233187957120820289523777

theorem tailTrace_4349118 : CollatzResearch.WordTrace tailWord_4349118 prefixEnd_4349118 2233187957120820289523777 := by
  unfold tailWord_4349118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19828170632236966383069001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105750243371930487376368005 19828170632236966383069001)
  ·
    refine ⟨14871127974177724787301751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19828170632236966383069001 14871127974177724787301751)
    ·
      refine ⟨22306691961266587180952627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14871127974177724787301751 22306691961266587180952627)
      ·
        refine ⟨33460037941899880771428941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22306691961266587180952627 33460037941899880771428941)
        ·
          refine ⟨12547514228212455289285853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33460037941899880771428941 12547514228212455289285853)
          ·
            refine ⟨4705317835579670733482195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12547514228212455289285853 4705317835579670733482195)
            ·
              refine ⟨7057976753369506100223293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705317835579670733482195 7057976753369506100223293)
              ·
                refine ⟨2646741282513564787583735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7057976753369506100223293 2646741282513564787583735)
                ·
                  refine ⟨3970111923770347181375603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646741282513564787583735 3970111923770347181375603)
                  ·
                    refine ⟨5955167885655520772063405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970111923770347181375603 5955167885655520772063405)
                    ·
                      refine ⟨2233187957120820289523777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955167885655520772063405 2233187957120820289523777)
                      ·
                        rfl

theorem cell23_4349118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_4349118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349118 prefixEnd_4349118 := by exact prefixLift 4349118
  have htrace : WordTrace (prefixWord ++ tailWord_4349118) baseStart_4349118 baseEnd_4349118 := by
    simpa [prefixWord, tailWord_4349118, baseEnd_4349118] using wordTrace_append hprefix tailTrace_4349118
  have hstable : (prefixWord ++ tailWord_4349118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349118).length < 2 ^ (prefixWord ++ tailWord_4349118).sum := by decide
  have hdescent : baseEnd_4349118 < baseStart_4349118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349130 : List Nat := [3, 1, 2, 1, 3, 4, 9]
def baseStart_4349130 : Nat := 118140960795 + 4349130 * 2 ^ 59
def prefixEnd_4349130 : Nat := 4983230072969 + 3 ^ 40 * 4349130 * 2
def baseEnd_4349130 : Nat := 27570297764057706698441

theorem tailTrace_4349130 : CollatzResearch.WordTrace tailWord_4349130 prefixEnd_4349130 27570297764057706698441 := by
  unfold tailWord_4349130
  simp only [CollatzResearch.WordTrace]
  refine ⟨39656450683463064278497211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105750535155901504742659229 39656450683463064278497211)
  ·
    refine ⟨59484676025194596417745817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39656450683463064278497211 59484676025194596417745817)
    ·
      refine ⟨44613507018895947313309363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59484676025194596417745817 44613507018895947313309363)
      ·
        refine ⟨66920260528343920969964045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44613507018895947313309363 66920260528343920969964045)
        ·
          refine ⟨25095097698128970363736517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66920260528343920969964045 25095097698128970363736517)
          ·
            refine ⟨4705330818399181943200597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25095097698128970363736517 4705330818399181943200597)
            ·
              refine ⟨27570297764057706698441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4705330818399181943200597 27570297764057706698441)
              ·
                rfl

theorem cell23_4349130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 9].length) (baseStart_4349130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349130 prefixEnd_4349130 := by exact prefixLift 4349130
  have htrace : WordTrace (prefixWord ++ tailWord_4349130) baseStart_4349130 baseEnd_4349130 := by
    simpa [prefixWord, tailWord_4349130, baseEnd_4349130] using wordTrace_append hprefix tailTrace_4349130
  have hstable : (prefixWord ++ tailWord_4349130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349130).length < 2 ^ (prefixWord ++ tailWord_4349130).sum := by decide
  have hdescent : baseEnd_4349130 < baseStart_4349130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349141 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4349141 : Nat := 118140960795 + 4349141 * 2 ^ 59
def prefixEnd_4349141 : Nat := 4983230072969 + 3 ^ 40 * 4349141 * 2
def baseEnd_4349141 : Nat := 2233199767175873699536171

theorem tailTrace_4349141 : CollatzResearch.WordTrace tailWord_4349141 prefixEnd_4349141 2233199767175873699536171 := by
  unfold tailWord_4349141
  simp only [CollatzResearch.WordTrace]
  refine ⟨158626203936812405992639277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105750802624541603995092851 158626203936812405992639277)
  ·
    refine ⟨59484826476304652247239729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158626203936812405992639277 59484826476304652247239729)
    ·
      refine ⟨44613619857228489185429797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59484826476304652247239729 44613619857228489185429797)
      ·
        refine ⟨8365053723230341722268087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44613619857228489185429797 8365053723230341722268087)
        ·
          refine ⟨12547580584845512583402131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8365053723230341722268087 12547580584845512583402131)
          ·
            refine ⟨18821370877268268875103197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12547580584845512583402131 18821370877268268875103197)
            ·
              refine ⟨7058014078975600828163699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18821370877268268875103197 7058014078975600828163699)
              ·
                refine ⟨10587021118463401242245549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7058014078975600828163699 10587021118463401242245549)
                ·
                  refine ⟨3970132919423775465842081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10587021118463401242245549 3970132919423775465842081)
                  ·
                    refine ⟨2977599689567831599381561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970132919423775465842081 2977599689567831599381561)
                    ·
                      refine ⟨2233199767175873699536171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977599689567831599381561 2233199767175873699536171)
                      ·
                        rfl

theorem cell23_4349141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4349141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349141 prefixEnd_4349141 := by exact prefixLift 4349141
  have htrace : WordTrace (prefixWord ++ tailWord_4349141) baseStart_4349141 baseEnd_4349141 := by
    simpa [prefixWord, tailWord_4349141, baseEnd_4349141] using wordTrace_append hprefix tailTrace_4349141
  have hstable : (prefixWord ++ tailWord_4349141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349141).length < 2 ^ (prefixWord ++ tailWord_4349141).sum := by decide
  have hdescent : baseEnd_4349141 < baseStart_4349141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349192 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_4349192 : Nat := 118140960795 + 4349192 * 2 ^ 59
def prefixEnd_4349192 : Nat := 4983230072969 + 3 ^ 40 * 4349192 * 2
def baseEnd_4349192 : Nat := 2233225954689252999998437

theorem tailTrace_4349192 : CollatzResearch.WordTrace tailWord_4349192 prefixEnd_4349192 2233225954689252999998437 := by
  unfold tailWord_4349192
  simp only [CollatzResearch.WordTrace]
  refine ⟨79314032029813820851372915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105752042706418427801830553 79314032029813820851372915)
  ·
    refine ⟨118971048044720731277059373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79314032029813820851372915 118971048044720731277059373)
    ·
      refine ⟨44614143016770274228897265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118971048044720731277059373 44614143016770274228897265)
      ·
        refine ⟨33460607262577705671672949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44614143016770274228897265 33460607262577705671672949)
        ·
          refine ⟨3136931930866659906719339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33460607262577705671672949 3136931930866659906719339)
          ·
            refine ⟨4705397896299989860079009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136931930866659906719339 4705397896299989860079009)
            ·
              refine ⟨3529048422224992395059257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705397896299989860079009 3529048422224992395059257)
              ·
                refine ⟨2646786316668744296294443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3529048422224992395059257 2646786316668744296294443)
                ·
                  refine ⟨3970179475003116444441665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646786316668744296294443 3970179475003116444441665)
                  ·
                    refine ⟨2977634606252337333331249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970179475003116444441665 2977634606252337333331249)
                    ·
                      refine ⟨2233225954689252999998437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977634606252337333331249 2233225954689252999998437)
                      ·
                        rfl

theorem cell23_4349192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_4349192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349192 prefixEnd_4349192 := by exact prefixLift 4349192
  have htrace : WordTrace (prefixWord ++ tailWord_4349192) baseStart_4349192 baseEnd_4349192 := by
    simpa [prefixWord, tailWord_4349192, baseEnd_4349192] using wordTrace_append hprefix tailTrace_4349192
  have hstable : (prefixWord ++ tailWord_4349192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349192).length < 2 ^ (prefixWord ++ tailWord_4349192).sum := by decide
  have hdescent : baseEnd_4349192 < baseStart_4349192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349247 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_4349247 : Nat := 118140960795 + 4349247 * 2 ^ 59
def prefixEnd_4349247 : Nat := 4983230072969 + 3 ^ 40 * 4349247 * 2
def baseEnd_4349247 : Nat := 2233254196125250284810683

theorem tailTrace_4349247 : CollatzResearch.WordTrace tailWord_4349247 prefixEnd_4349247 2233254196125250284810683 := by
  unfold tailWord_4349247
  simp only [CollatzResearch.WordTrace]
  refine ⟨158630070074428386095997995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105753380049618924063998663 158630070074428386095997995)
  ·
    refine ⟨237945105111642579143996993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158630070074428386095997995 237945105111642579143996993)
    ·
      refine ⟨178458828833731934357997745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237945105111642579143996993 178458828833731934357997745)
      ·
        refine ⟨133844121625298950768498309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178458828833731934357997745 133844121625298950768498309)
        ·
          refine ⟨25095772804743553269093433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133844121625298950768498309 25095772804743553269093433)
          ·
            refine ⟨18821829603557664951820075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25095772804743553269093433 18821829603557664951820075)
            ·
              refine ⟨28232744405336497427730113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18821829603557664951820075 28232744405336497427730113)
              ·
                refine ⟨21174558304002373070797585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28232744405336497427730113 21174558304002373070797585)
                ·
                  refine ⟨15880918728001779803098189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21174558304002373070797585 15880918728001779803098189)
                  ·
                    refine ⟨5955344523000667426161821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15880918728001779803098189 5955344523000667426161821)
                    ·
                      refine ⟨2233254196125250284810683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955344523000667426161821 2233254196125250284810683)
                      ·
                        rfl

theorem cell23_4349247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_4349247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349247 prefixEnd_4349247 := by exact prefixLift 4349247
  have htrace : WordTrace (prefixWord ++ tailWord_4349247) baseStart_4349247 baseEnd_4349247 := by
    simpa [prefixWord, tailWord_4349247, baseEnd_4349247] using wordTrace_append hprefix tailTrace_4349247
  have hstable : (prefixWord ++ tailWord_4349247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349247).length < 2 ^ (prefixWord ++ tailWord_4349247).sum := by decide
  have hdescent : baseEnd_4349247 < baseStart_4349247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349257 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 7, 2]
def baseStart_4349257 : Nat := 118140960795 + 4349257 * 2 ^ 59
def prefixEnd_4349257 : Nat := 4983230072969 + 3 ^ 40 * 4349257 * 2
def baseEnd_4349257 : Nat := 2233259330931795245685637

theorem tailTrace_4349257 : CollatzResearch.WordTrace tailWord_4349257 prefixEnd_4349257 2233259330931795245685637 := by
  unfold tailWord_4349257
  simp only [CollatzResearch.WordTrace]
  refine ⟨158630434804392157803862025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105753623202928105202574683 158630434804392157803862025)
  ·
    refine ⟨118972826103294118352896519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158630434804392157803862025 118972826103294118352896519)
    ·
      refine ⟨178459239154941177529344779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118972826103294118352896519 178459239154941177529344779)
      ·
        refine ⟨267688858732411766294017169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178459239154941177529344779 267688858732411766294017169)
        ·
          refine ⟨200766644049308824720512877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267688858732411766294017169 200766644049308824720512877)
          ·
            refine ⟨75287491518490809270192329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200766644049308824720512877 75287491518490809270192329)
            ·
              refine ⟨56465618638868106952644247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75287491518490809270192329 56465618638868106952644247)
              ·
                refine ⟨84698427958302160428966371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56465618638868106952644247 84698427958302160428966371)
                ·
                  refine ⟨127047641937453240643449557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84698427958302160428966371 127047641937453240643449557)
                  ·
                    refine ⟨2977679107909060327580849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127047641937453240643449557 2977679107909060327580849)
                    ·
                      refine ⟨2233259330931795245685637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977679107909060327580849 2233259330931795245685637)
                      ·
                        rfl

theorem cell23_4349257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 7, 2].length) (baseStart_4349257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349257 prefixEnd_4349257 := by exact prefixLift 4349257
  have htrace : WordTrace (prefixWord ++ tailWord_4349257) baseStart_4349257 baseEnd_4349257 := by
    simpa [prefixWord, tailWord_4349257, baseEnd_4349257] using wordTrace_append hprefix tailTrace_4349257
  have hstable : (prefixWord ++ tailWord_4349257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349257).length < 2 ^ (prefixWord ++ tailWord_4349257).sum := by decide
  have hdescent : baseEnd_4349257 < baseStart_4349257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349288 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 5]
def baseStart_4349288 : Nat := 118140960795 + 4349288 * 2 ^ 59
def prefixEnd_4349288 : Nat := 4983230072969 + 3 ^ 40 * 4349288 * 2
def baseEnd_4349288 : Nat := 248141694314676069377555

theorem tailTrace_4349288 : CollatzResearch.WordTrace tailWord_4349288 prefixEnd_4349288 248141694314676069377555 := by
  unfold tailWord_4349288
  simp only [CollatzResearch.WordTrace]
  refine ⟨79315782733639925049120259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105754376978186566732160345 79315782733639925049120259)
  ·
    refine ⟨118973674100459887573680389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79315782733639925049120259 118973674100459887573680389)
    ·
      refine ⟨22307563893836228920065073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118973674100459887573680389 22307563893836228920065073)
      ·
        refine ⟨16730672920377171690048805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22307563893836228920065073 16730672920377171690048805)
        ·
          refine ⟨3137001172570719691884151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16730672920377171690048805 3137001172570719691884151)
          ·
            refine ⟨4705501758856079537826227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137001172570719691884151 4705501758856079537826227)
            ·
              refine ⟨7058252638284119306739341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705501758856079537826227 7058252638284119306739341)
              ·
                refine ⟨2646844739356544740027253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7058252638284119306739341 2646844739356544740027253)
                ·
                  refine ⟨248141694314676069377555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646844739356544740027253 248141694314676069377555)
                  ·
                    rfl

theorem cell23_4349288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 5].length) (baseStart_4349288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349288 prefixEnd_4349288 := by exact prefixLift 4349288
  have htrace : WordTrace (prefixWord ++ tailWord_4349288) baseStart_4349288 baseEnd_4349288 := by
    simpa [prefixWord, tailWord_4349288, baseEnd_4349288] using wordTrace_append hprefix tailTrace_4349288
  have hstable : (prefixWord ++ tailWord_4349288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349288).length < 2 ^ (prefixWord ++ tailWord_4349288).sum := by decide
  have hdescent : baseEnd_4349288 < baseStart_4349288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349297 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 5, 4]
def baseStart_4349297 : Nat := 118140960795 + 4349297 * 2 ^ 59
def prefixEnd_4349297 : Nat := 4983230072969 + 3 ^ 40 * 4349297 * 2
def baseEnd_4349297 : Nat := 744426623385991696395151

theorem tailTrace_4349297 : CollatzResearch.WordTrace tailWord_4349297 prefixEnd_4349297 744426623385991696395151 := by
  unfold tailWord_4349297
  simp only [CollatzResearch.WordTrace]
  refine ⟨158631893724247244635318145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105754595816164829756878763 158631893724247244635318145)
  ·
    refine ⟨118973920293185433476488609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158631893724247244635318145 118973920293185433476488609)
    ·
      refine ⟨89230440219889075107366457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118973920293185433476488609 89230440219889075107366457)
      ·
        refine ⟨66922830164916806330524843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89230440219889075107366457 66922830164916806330524843)
        ·
          refine ⟨100384245247375209495787265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66922830164916806330524843 100384245247375209495787265)
          ·
            refine ⟨75288183935531407121840449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100384245247375209495787265 75288183935531407121840449)
            ·
              refine ⟨56466137951648555341380337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75288183935531407121840449 56466137951648555341380337)
              ·
                refine ⟨42349603463736416506035253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56466137951648555341380337 42349603463736416506035253)
                ·
                  refine ⟨3970275324725289047440805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42349603463736416506035253 3970275324725289047440805)
                  ·
                    refine ⟨744426623385991696395151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970275324725289047440805 744426623385991696395151)
                    ·
                      rfl

theorem cell23_4349297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_4349297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349297 prefixEnd_4349297 := by exact prefixLift 4349297
  have htrace : WordTrace (prefixWord ++ tailWord_4349297) baseStart_4349297 baseEnd_4349297 := by
    simpa [prefixWord, tailWord_4349297, baseEnd_4349297] using wordTrace_append hprefix tailTrace_4349297
  have hstable : (prefixWord ++ tailWord_4349297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349297).length < 2 ^ (prefixWord ++ tailWord_4349297).sum := by decide
  have hdescent : baseEnd_4349297 < baseStart_4349297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349341 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_4349341 : Nat := 118140960795 + 4349341 * 2 ^ 59
def prefixEnd_4349341 : Nat := 4983230072969 + 3 ^ 40 * 4349341 * 2
def baseEnd_4349341 : Nat := 2233302463306772917035251

theorem tailTrace_4349341 : CollatzResearch.WordTrace tailWord_4349341 prefixEnd_4349341 2233302463306772917035251 := by
  unfold tailWord_4349341
  simp only [CollatzResearch.WordTrace]
  refine ⟨158633498536087840149919877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105755665690725226766613251 158633498536087840149919877)
  ·
    refine ⟨29743780975516470028109977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158633498536087840149919877 29743780975516470028109977)
    ·
      refine ⟨22307835731637352521082483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29743780975516470028109977 22307835731637352521082483)
      ·
        refine ⟨33461753597456028781623725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22307835731637352521082483 33461753597456028781623725)
        ·
          refine ⟨12548157599046010793108897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33461753597456028781623725 12548157599046010793108897)
          ·
            refine ⟨9411118199284508094831673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12548157599046010793108897 9411118199284508094831673)
            ·
              refine ⟨7058338649463381071123755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9411118199284508094831673 7058338649463381071123755)
              ·
                refine ⟨10587507974195071606685633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7058338649463381071123755 10587507974195071606685633)
                ·
                  refine ⟨7940630980646303705014225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10587507974195071606685633 7940630980646303705014225)
                  ·
                    refine ⟨5955473235484727778760669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7940630980646303705014225 5955473235484727778760669)
                    ·
                      refine ⟨2233302463306772917035251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955473235484727778760669 2233302463306772917035251)
                      ·
                        rfl

theorem cell23_4349341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_4349341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349341 prefixEnd_4349341 := by exact prefixLift 4349341
  have htrace : WordTrace (prefixWord ++ tailWord_4349341) baseStart_4349341 baseEnd_4349341 := by
    simpa [prefixWord, tailWord_4349341, baseEnd_4349341] using wordTrace_append hprefix tailTrace_4349341
  have hstable : (prefixWord ++ tailWord_4349341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349341).length < 2 ^ (prefixWord ++ tailWord_4349341).sum := by decide
  have hdescent : baseEnd_4349341 < baseStart_4349341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349365 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_4349365 : Nat := 118140960795 + 4349365 * 2 ^ 59
def prefixEnd_4349365 : Nat := 4983230072969 + 3 ^ 40 * 4349365 * 2
def baseEnd_4349365 : Nat := 744438262280826941045047

theorem tailTrace_4349365 : CollatzResearch.WordTrace tailWord_4349365 prefixEnd_4349365 744438262280826941045047 := by
  unfold tailWord_4349365
  simp only [CollatzResearch.WordTrace]
  refine ⟨158634373888000892248793549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105756249258667261499195699 158634373888000892248793549)
  ·
    refine ⟨59487890208000334593297581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158634373888000892248793549 59487890208000334593297581)
    ·
      refine ⟨22307958828000125472486593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59487890208000334593297581 22307958828000125472486593)
      ·
        refine ⟨16730969121000094104364945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22307958828000125472486593 16730969121000094104364945)
        ·
          refine ⟨12548226840750070578273709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16730969121000094104364945 12548226840750070578273709)
          ·
            refine ⟨4705585065281276466852641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12548226840750070578273709 4705585065281276466852641)
            ·
              refine ⟨3529188798960957350139481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705585065281276466852641 3529188798960957350139481)
              ·
                refine ⟨2646891599220718012604611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3529188798960957350139481 2646891599220718012604611)
                ·
                  refine ⟨3970337398831077018906917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646891599220718012604611 3970337398831077018906917)
                  ·
                    refine ⟨744438262280826941045047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970337398831077018906917 744438262280826941045047)
                    ·
                      rfl

theorem cell23_4349365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_4349365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349365 prefixEnd_4349365 := by exact prefixLift 4349365
  have htrace : WordTrace (prefixWord ++ tailWord_4349365) baseStart_4349365 baseEnd_4349365 := by
    simpa [prefixWord, tailWord_4349365, baseEnd_4349365] using wordTrace_append hprefix tailTrace_4349365
  have hstable : (prefixWord ++ tailWord_4349365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349365).length < 2 ^ (prefixWord ++ tailWord_4349365).sum := by decide
  have hdescent : baseEnd_4349365 < baseStart_4349365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349387 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 1, 6]
def baseStart_4349387 : Nat := 118140960795 + 4349387 * 2 ^ 59
def prefixEnd_4349387 : Nat := 4983230072969 + 3 ^ 40 * 4349387 * 2
def baseEnd_4349387 : Nat := 744442027805626579020013

theorem tailTrace_4349387 : CollatzResearch.WordTrace tailWord_4349387 prefixEnd_4349387 744442027805626579020013 := by
  unfold tailWord_4349387
  simp only [CollatzResearch.WordTrace]
  refine ⟨158635176293921190006094415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105756784195947460004062943 158635176293921190006094415)
  ·
    refine ⟨237952764440881785009141623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158635176293921190006094415 237952764440881785009141623)
    ·
      refine ⟨356929146661322677513712435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237952764440881785009141623 356929146661322677513712435)
      ·
        refine ⟨535393719991984016270568653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356929146661322677513712435 535393719991984016270568653)
        ·
          refine ⟨200772644996994006101463245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535393719991984016270568653 200772644996994006101463245)
          ·
            refine ⟨75289741873872752288048717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200772644996994006101463245 75289741873872752288048717)
            ·
              refine ⟨28233653202702282108018269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75289741873872752288048717 28233653202702282108018269)
              ·
                refine ⟨10587619951013355790506851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28233653202702282108018269 10587619951013355790506851)
                ·
                  refine ⟨15881429926520033685760277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10587619951013355790506851 15881429926520033685760277)
                  ·
                    refine ⟨744442027805626579020013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15881429926520033685760277 744442027805626579020013)
                    ·
                      rfl

theorem cell23_4349387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 6].length) (baseStart_4349387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349387 prefixEnd_4349387 := by exact prefixLift 4349387
  have htrace : WordTrace (prefixWord ++ tailWord_4349387) baseStart_4349387 baseEnd_4349387 := by
    simpa [prefixWord, tailWord_4349387, baseEnd_4349387] using wordTrace_append hprefix tailTrace_4349387
  have hstable : (prefixWord ++ tailWord_4349387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349387).length < 2 ^ (prefixWord ++ tailWord_4349387).sum := by decide
  have hdescent : baseEnd_4349387 < baseStart_4349387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349398 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4349398 : Nat := 118140960795 + 4349398 * 2 ^ 59
def prefixEnd_4349398 : Nat := 4983230072969 + 3 ^ 40 * 4349398 * 2
def baseEnd_4349398 : Nat := 2233331731704079194022489

theorem tailTrace_4349398 : CollatzResearch.WordTrace tailWord_4349398 prefixEnd_4349398 2233331731704079194022489 := by
  unfold tailWord_4349398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914723593555083680296553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105757051664587559256496565 9914723593555083680296553)
  ·
    refine ⟨7436042695166312760222415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9914723593555083680296553 7436042695166312760222415)
    ·
      refine ⟨11154064042749469140333623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7436042695166312760222415 11154064042749469140333623)
      ·
        refine ⟨16731096064124203710500435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154064042749469140333623 16731096064124203710500435)
        ·
          refine ⟨25096644096186305565750653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16731096064124203710500435 25096644096186305565750653)
          ·
            refine ⟨9411241536069864587156495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25096644096186305565750653 9411241536069864587156495)
            ·
              refine ⟨14116862304104796880734743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9411241536069864587156495 14116862304104796880734743)
              ·
                refine ⟨21175293456157195321102115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14116862304104796880734743 21175293456157195321102115)
                ·
                  refine ⟨31762940184235792981653173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21175293456157195321102115 31762940184235792981653173)
                  ·
                    refine ⟨2977775642272105592029985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31762940184235792981653173 2977775642272105592029985)
                    ·
                      refine ⟨2233331731704079194022489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977775642272105592029985 2233331731704079194022489)
                      ·
                        rfl

theorem cell23_4349398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4349398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349398 prefixEnd_4349398 := by exact prefixLift 4349398
  have htrace : WordTrace (prefixWord ++ tailWord_4349398) baseStart_4349398 baseEnd_4349398 := by
    simpa [prefixWord, tailWord_4349398, baseEnd_4349398] using wordTrace_append hprefix tailTrace_4349398
  have hstable : (prefixWord ++ tailWord_4349398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349398).length < 2 ^ (prefixWord ++ tailWord_4349398).sum := by decide
  have hdescent : baseEnd_4349398 < baseStart_4349398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349405 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_4349405 : Nat := 118140960795 + 4349405 * 2 ^ 59
def prefixEnd_4349405 : Nat := 4983230072969 + 3 ^ 40 * 4349405 * 2
def baseEnd_4349405 : Nat := 2233335326068660666634957

theorem tailTrace_4349405 : CollatzResearch.WordTrace tailWord_4349405 prefixEnd_4349405 2233335326068660666634957 := by
  unfold tailWord_4349405
  simp only [CollatzResearch.WordTrace]
  refine ⟨158635832807855979080249669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105757221871903986053499779 158635832807855979080249669)
  ·
    refine ⟨29744218651472996077546813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158635832807855979080249669 29744218651472996077546813)
    ·
      refine ⟨11154081994302373529080055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29744218651472996077546813 11154081994302373529080055)
      ·
        refine ⟨16731122991453560293620083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154081994302373529080055 16731122991453560293620083)
        ·
          refine ⟨25096684487180340440430125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16731122991453560293620083 25096684487180340440430125)
          ·
            refine ⟨9411256682692627665161297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25096684487180340440430125 9411256682692627665161297)
            ·
              refine ⟨7058442512019470748870973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9411256682692627665161297 7058442512019470748870973)
              ·
                refine ⟨2646915942007301530826615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7058442512019470748870973 2646915942007301530826615)
                ·
                  refine ⟨3970373913010952296239923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646915942007301530826615 3970373913010952296239923)
                  ·
                    refine ⟨5955560869516428444359885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970373913010952296239923 5955560869516428444359885)
                    ·
                      refine ⟨2233335326068660666634957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955560869516428444359885 2233335326068660666634957)
                      ·
                        rfl

theorem cell23_4349405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_4349405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349405 prefixEnd_4349405 := by exact prefixLift 4349405
  have htrace : WordTrace (prefixWord ++ tailWord_4349405) baseStart_4349405 baseEnd_4349405 := by
    simpa [prefixWord, tailWord_4349405, baseEnd_4349405] using wordTrace_append hprefix tailTrace_4349405
  have hstable : (prefixWord ++ tailWord_4349405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349405).length < 2 ^ (prefixWord ++ tailWord_4349405).sum := by decide
  have hdescent : baseEnd_4349405 < baseStart_4349405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349411 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 4]
def baseStart_4349411 : Nat := 118140960795 + 4349411 * 2 ^ 59
def prefixEnd_4349411 : Nat := 4983230072969 + 3 ^ 40 * 4349411 * 2
def baseEnd_4349411 : Nat := 2233338406952587643159929

theorem tailTrace_4349411 : CollatzResearch.WordTrace tailWord_4349411 prefixEnd_4349411 2233338406952587643159929 := by
  unfold tailWord_4349411
  simp only [CollatzResearch.WordTrace]
  refine ⟨158636051645834242104968087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105757367763889494736645391 158636051645834242104968087)
  ·
    refine ⟨237954077468751363157452131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158636051645834242104968087 237954077468751363157452131)
    ·
      refine ⟨356931116203127044736178197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237954077468751363157452131 356931116203127044736178197)
      ·
        refine ⟨16731146072021580222008353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 356931116203127044736178197 16731146072021580222008353)
        ·
          refine ⟨12548359554016185166506265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16731146072021580222008353 12548359554016185166506265)
          ·
            refine ⟨9411269665512138874879699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12548359554016185166506265 9411269665512138874879699)
            ·
              refine ⟨14116904498268208312319549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9411269665512138874879699 14116904498268208312319549)
              ·
                refine ⟨5293839186850578117119831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14116904498268208312319549 5293839186850578117119831)
                ·
                  refine ⟨7940758780275867175679747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5293839186850578117119831 7940758780275867175679747)
                  ·
                    refine ⟨11911138170413800763519621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7940758780275867175679747 11911138170413800763519621)
                    ·
                      refine ⟨2233338406952587643159929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11911138170413800763519621 2233338406952587643159929)
                      ·
                        rfl

theorem cell23_4349411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_4349411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349411 prefixEnd_4349411 := by exact prefixLift 4349411
  have htrace : WordTrace (prefixWord ++ tailWord_4349411) baseStart_4349411 baseEnd_4349411 := by
    simpa [prefixWord, tailWord_4349411, baseEnd_4349411] using wordTrace_append hprefix tailTrace_4349411
  have hstable : (prefixWord ++ tailWord_4349411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349411).length < 2 ^ (prefixWord ++ tailWord_4349411).sum := by decide
  have hdescent : baseEnd_4349411 < baseStart_4349411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349451 : List Nat := [1, 1, 1, 1, 8, 2, 2, 7]
def baseStart_4349451 : Nat := 118140960795 + 4349451 * 2 ^ 59
def prefixEnd_4349451 : Nat := 4983230072969 + 3 ^ 40 * 4349451 * 2
def baseEnd_4349451 : Nat := 82716998006621018024435

theorem tailTrace_4349451 : CollatzResearch.WordTrace tailWord_4349451 prefixEnd_4349451 82716998006621018024435 := by
  unfold tailWord_4349451
  simp only [CollatzResearch.WordTrace]
  refine ⟨158637510565689328936424207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105758340377126219290949471 158637510565689328936424207)
  ·
    refine ⟨237956265848533993404636311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158637510565689328936424207 237956265848533993404636311)
    ·
      refine ⟨356934398772800990106954467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237956265848533993404636311 356934398772800990106954467)
      ·
        refine ⟨535401598159201485160431701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356934398772800990106954467 535401598159201485160431701)
        ·
          refine ⟨6274237478428142404223809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 535401598159201485160431701 6274237478428142404223809)
          ·
            refine ⟨4705678108821106803167857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6274237478428142404223809 4705678108821106803167857)
            ·
              refine ⟨3529258581615830102375893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705678108821106803167857 3529258581615830102375893)
              ·
                refine ⟨82716998006621018024435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3529258581615830102375893 82716998006621018024435)
                ·
                  rfl

theorem cell23_4349451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 7].length) (baseStart_4349451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349451 prefixEnd_4349451 := by exact prefixLift 4349451
  have htrace : WordTrace (prefixWord ++ tailWord_4349451) baseStart_4349451 baseEnd_4349451 := by
    simpa [prefixWord, tailWord_4349451, baseEnd_4349451] using wordTrace_append hprefix tailTrace_4349451
  have hstable : (prefixWord ++ tailWord_4349451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349451).length < 2 ^ (prefixWord ++ tailWord_4349451).sum := by decide
  have hdescent : baseEnd_4349451 < baseStart_4349451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349457 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_4349457 : Nat := 118140960795 + 4349457 * 2 ^ 59
def prefixEnd_4349457 : Nat := 4983230072969 + 3 ^ 40 * 4349457 * 2
def baseEnd_4349457 : Nat := 2233362027062694463184717

theorem tailTrace_4349457 : CollatzResearch.WordTrace tailWord_4349457 prefixEnd_4349457 2233362027062694463184717 := by
  unfold tailWord_4349457
  simp only [CollatzResearch.WordTrace]
  refine ⟨158637729403667591961142625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105758486269111727974095083 158637729403667591961142625)
  ·
    refine ⟨118978297052750693970856969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158637729403667591961142625 118978297052750693970856969)
    ·
      refine ⟨89233722789563020478142727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118978297052750693970856969 89233722789563020478142727)
      ·
        refine ⟨133850584184344530717214091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89233722789563020478142727 133850584184344530717214091)
        ·
          refine ⟨200775876276516796075821137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133850584184344530717214091 200775876276516796075821137)
          ·
            refine ⟨150581907207387597056865853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200775876276516796075821137 150581907207387597056865853)
            ·
              refine ⟨56468215202770348896324695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150581907207387597056865853 56468215202770348896324695)
              ·
                refine ⟨84702322804155523344487043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56468215202770348896324695 84702322804155523344487043)
                ·
                  refine ⟨127053484206233285016730565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84702322804155523344487043 127053484206233285016730565)
                  ·
                    refine ⟨23822528288668740940636981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127053484206233285016730565 23822528288668740940636981)
                    ·
                      refine ⟨2233362027062694463184717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23822528288668740940636981 2233362027062694463184717)
                      ·
                        rfl

theorem cell23_4349457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_4349457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349457 prefixEnd_4349457 := by exact prefixLift 4349457
  have htrace : WordTrace (prefixWord ++ tailWord_4349457) baseStart_4349457 baseEnd_4349457 := by
    simpa [prefixWord, tailWord_4349457, baseEnd_4349457] using wordTrace_append hprefix tailTrace_4349457
  have hstable : (prefixWord ++ tailWord_4349457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349457).length < 2 ^ (prefixWord ++ tailWord_4349457).sum := by decide
  have hdescent : baseEnd_4349457 < baseStart_4349457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349461 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_4349461 : Nat := 118140960795 + 4349461 * 2 ^ 59
def prefixEnd_4349461 : Nat := 4983230072969 + 3 ^ 40 * 4349461 * 2
def baseEnd_4349461 : Nat := 2233364080985312447534699

theorem tailTrace_4349461 : CollatzResearch.WordTrace tailWord_4349461 prefixEnd_4349461 2233364080985312447534699 := by
  unfold tailWord_4349461
  simp only [CollatzResearch.WordTrace]
  refine ⟨158637875295653100644288237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105758583530435400429525491 158637875295653100644288237)
  ·
    refine ⟨59489203235869912741608089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158637875295653100644288237 59489203235869912741608089)
    ·
      refine ⟨44616902426902434556206067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59489203235869912741608089 44616902426902434556206067)
      ·
        refine ⟨66925353640353651834309101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44616902426902434556206067 66925353640353651834309101)
        ·
          refine ⟨25097007615132619437865913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66925353640353651834309101 25097007615132619437865913)
          ·
            refine ⟨18822755711349464578399435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25097007615132619437865913 18822755711349464578399435)
            ·
              refine ⟨28234133567024196867599153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18822755711349464578399435 28234133567024196867599153)
              ·
                refine ⟨21175600175268147650699365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28234133567024196867599153 21175600175268147650699365)
                ·
                  refine ⟨3970425032862777684506131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21175600175268147650699365 3970425032862777684506131)
                  ·
                    refine ⟨5955637549294166526759197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970425032862777684506131 5955637549294166526759197)
                    ·
                      refine ⟨2233364080985312447534699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955637549294166526759197 2233364080985312447534699)
                      ·
                        rfl

theorem cell23_4349461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_4349461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349461 prefixEnd_4349461 := by exact prefixLift 4349461
  have htrace : WordTrace (prefixWord ++ tailWord_4349461) baseStart_4349461 baseEnd_4349461 := by
    simpa [prefixWord, tailWord_4349461, baseEnd_4349461] using wordTrace_append hprefix tailTrace_4349461
  have hstable : (prefixWord ++ tailWord_4349461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349461).length < 2 ^ (prefixWord ++ tailWord_4349461).sum := by decide
  have hdescent : baseEnd_4349461 < baseStart_4349461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349495 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 2, 1, 3]
def baseStart_4349495 : Nat := 118140960795 + 4349495 * 2 ^ 59
def prefixEnd_4349495 : Nat := 4983230072969 + 3 ^ 40 * 4349495 * 2
def baseEnd_4349495 : Nat := 2233381539327565314509543

theorem tailTrace_4349495 : CollatzResearch.WordTrace tailWord_4349495 prefixEnd_4349495 2233381539327565314509543 := by
  unfold tailWord_4349495
  simp only [CollatzResearch.WordTrace]
  refine ⟨158639115377529924451025939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105759410251686616300683959 158639115377529924451025939)
  ·
    refine ⟨237958673066294886676538909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158639115377529924451025939 237958673066294886676538909)
    ·
      refine ⟨89234502399860582503702091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237958673066294886676538909 89234502399860582503702091)
      ·
        refine ⟨133851753599790873755553137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89234502399860582503702091 133851753599790873755553137)
        ·
          refine ⟨100388815199843155316664853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133851753599790873755553137 100388815199843155316664853)
          ·
            refine ⟨4705725712492647905468665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100388815199843155316664853 4705725712492647905468665)
            ·
              refine ⟨3529294284369485929101499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705725712492647905468665 3529294284369485929101499)
              ·
                refine ⟨5293941426554228893652249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529294284369485929101499 5293941426554228893652249)
                ·
                  refine ⟨3970456069915671670239187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5293941426554228893652249 3970456069915671670239187)
                  ·
                    refine ⟨5955684104873507505358781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970456069915671670239187 5955684104873507505358781)
                    ·
                      refine ⟨2233381539327565314509543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955684104873507505358781 2233381539327565314509543)
                      ·
                        rfl

theorem cell23_4349495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_4349495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349495 prefixEnd_4349495 := by exact prefixLift 4349495
  have htrace : WordTrace (prefixWord ++ tailWord_4349495) baseStart_4349495 baseEnd_4349495 := by
    simpa [prefixWord, tailWord_4349495, baseEnd_4349495] using wordTrace_append hprefix tailTrace_4349495
  have hstable : (prefixWord ++ tailWord_4349495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349495).length < 2 ^ (prefixWord ++ tailWord_4349495).sum := by decide
  have hdescent : baseEnd_4349495 < baseStart_4349495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349561 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 2, 5, 2]
def baseStart_4349561 : Nat := 118140960795 + 4349561 * 2 ^ 59
def prefixEnd_4349561 : Nat := 4983230072969 + 3 ^ 40 * 4349561 * 2
def baseEnd_4349561 : Nat := 2233415429050762056284239

theorem tailTrace_4349561 : CollatzResearch.WordTrace tailWord_4349561 prefixEnd_4349561 2233415429050762056284239 := by
  unfold tailWord_4349561
  simp only [CollatzResearch.WordTrace]
  refine ⟨158641522595290817722928537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105761015063527211815285691 158641522595290817722928537)
  ·
    refine ⟨118981141946468113292196403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158641522595290817722928537 118981141946468113292196403)
    ·
      refine ⟨178471712919702169938294605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118981141946468113292196403 178471712919702169938294605)
      ·
        refine ⟨66926892344888313726860477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178471712919702169938294605 66926892344888313726860477)
        ·
          refine ⟨25097584629333117647572679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66926892344888313726860477 25097584629333117647572679)
          ·
            refine ⟨37646376943999676471359019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25097584629333117647572679 37646376943999676471359019)
            ·
              refine ⟨56469565415999514707038529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37646376943999676471359019 56469565415999514707038529)
              ·
                refine ⟨42352174061999636030278897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56469565415999514707038529 42352174061999636030278897)
                ·
                  refine ⟨31764130546499727022709173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42352174061999636030278897 31764130546499727022709173)
                  ·
                    refine ⟨2977887238734349408378985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31764130546499727022709173 2977887238734349408378985)
                    ·
                      refine ⟨2233415429050762056284239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977887238734349408378985 2233415429050762056284239)
                      ·
                        rfl

theorem cell23_4349561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_4349561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349561 prefixEnd_4349561 := by exact prefixLift 4349561
  have htrace : WordTrace (prefixWord ++ tailWord_4349561) baseStart_4349561 baseEnd_4349561 := by
    simpa [prefixWord, tailWord_4349561, baseEnd_4349561] using wordTrace_append hprefix tailTrace_4349561
  have hstable : (prefixWord ++ tailWord_4349561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349561).length < 2 ^ (prefixWord ++ tailWord_4349561).sum := by decide
  have hdescent : baseEnd_4349561 < baseStart_4349561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349645 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4349645 : Nat := 118140960795 + 4349645 * 2 ^ 59
def prefixEnd_4349645 : Nat := 4983230072969 + 3 ^ 40 * 4349645 * 2
def baseEnd_4349645 : Nat := 2233458561425739727633853

theorem tailTrace_4349645 : CollatzResearch.WordTrace tailWord_4349645 prefixEnd_4349645 2233458561425739727633853 := by
  unfold tailWord_4349645
  simp only [CollatzResearch.WordTrace]
  refine ⟨158644586326986500068986389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105763057551324333379324259 158644586326986500068986389)
  ·
    refine ⟨7436464984077492190733737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158644586326986500068986389 7436464984077492190733737)
    ·
      refine ⟨5577348738058119143050303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7436464984077492190733737 5577348738058119143050303)
      ·
        refine ⟨8366023107087178714575455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577348738058119143050303 8366023107087178714575455)
        ·
          refine ⟨12549034660630768071863183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366023107087178714575455 12549034660630768071863183)
          ·
            refine ⟨18823551990946152107794775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12549034660630768071863183 18823551990946152107794775)
            ·
              refine ⟨28235327986419228161692163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18823551990946152107794775 28235327986419228161692163)
              ·
                refine ⟨42352991979628842242538245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28235327986419228161692163 42352991979628842242538245)
                ·
                  refine ⟨7941185996180407920475921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42352991979628842242538245 7941185996180407920475921)
                  ·
                    refine ⟨5955889497135305940356941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7941185996180407920475921 5955889497135305940356941)
                    ·
                      refine ⟨2233458561425739727633853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5955889497135305940356941 2233458561425739727633853)
                      ·
                        rfl

theorem cell23_4349645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4349645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349645 prefixEnd_4349645 := by exact prefixLift 4349645
  have htrace : WordTrace (prefixWord ++ tailWord_4349645) baseStart_4349645 baseEnd_4349645 := by
    simpa [prefixWord, tailWord_4349645, baseEnd_4349645] using wordTrace_append hprefix tailTrace_4349645
  have hstable : (prefixWord ++ tailWord_4349645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349645).length < 2 ^ (prefixWord ++ tailWord_4349645).sum := by decide
  have hdescent : baseEnd_4349645 < baseStart_4349645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349665 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 6]
def baseStart_4349665 : Nat := 118140960795 + 4349665 * 2 ^ 59
def prefixEnd_4349665 : Nat := 4983230072969 + 3 ^ 40 * 4349665 * 2
def baseEnd_4349665 : Nat := 248163203448758849931529

theorem tailTrace_4349665 : CollatzResearch.WordTrace tailWord_4349665 prefixEnd_4349665 248163203448758849931529 := by
  unfold tailWord_4349665
  simp only [CollatzResearch.WordTrace]
  refine ⟨158645315786914043484714449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105763543857942695656476299 158645315786914043484714449)
  ·
    refine ⟨118983986840185532613535837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158645315786914043484714449 118983986840185532613535837)
    ·
      refine ⟨44618995065069574730075939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118983986840185532613535837 44618995065069574730075939)
      ·
        refine ⟨66928492597604362095113909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44618995065069574730075939 66928492597604362095113909)
        ·
          refine ⟨6274546181025408946416929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66928492597604362095113909 6274546181025408946416929)
          ·
            refine ⟨4705909635769056709812697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6274546181025408946416929 4705909635769056709812697)
            ·
              refine ⟨3529432226826792532359523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705909635769056709812697 3529432226826792532359523)
              ·
                refine ⟨5294148340240188798539285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529432226826792532359523 5294148340240188798539285)
                ·
                  refine ⟨248163203448758849931529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5294148340240188798539285 248163203448758849931529)
                  ·
                    rfl

theorem cell23_4349665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 6].length) (baseStart_4349665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349665 prefixEnd_4349665 := by exact prefixLift 4349665
  have htrace : WordTrace (prefixWord ++ tailWord_4349665) baseStart_4349665 baseEnd_4349665 := by
    simpa [prefixWord, tailWord_4349665, baseEnd_4349665] using wordTrace_append hprefix tailTrace_4349665
  have hstable : (prefixWord ++ tailWord_4349665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349665).length < 2 ^ (prefixWord ++ tailWord_4349665).sum := by decide
  have hdescent : baseEnd_4349665 < baseStart_4349665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349668 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_4349668 : Nat := 118140960795 + 4349668 * 2 ^ 59
def prefixEnd_4349668 : Nat := 4983230072969 + 3 ^ 40 * 4349668 * 2
def baseEnd_4349668 : Nat := 2233470371480793137646247

theorem tailTrace_4349668 : CollatzResearch.WordTrace tailWord_4349668 prefixEnd_4349668 2233470371480793137646247 := by
  unfold tailWord_4349668
  simp only [CollatzResearch.WordTrace]
  refine ⟨79322712602951587498536829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105763616803935449998049105 79322712602951587498536829)
  ·
    refine ⟨29746017226106845311951311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79322712602951587498536829 29746017226106845311951311)
    ·
      refine ⟨44619025839160267967926967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29746017226106845311951311 44619025839160267967926967)
      ·
        refine ⟨66928538758740401951890451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44619025839160267967926967 66928538758740401951890451)
        ·
          refine ⟨100392808138110602927835677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66928538758740401951890451 100392808138110602927835677)
          ·
            refine ⟨37647303051791476097938379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100392808138110602927835677 37647303051791476097938379)
            ·
              refine ⟨56470954577687214146907569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37647303051791476097938379 56470954577687214146907569)
              ·
                refine ⟨42353215933265410610180677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56470954577687214146907569 42353215933265410610180677)
                ·
                  refine ⟨7941227987487264489408877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42353215933265410610180677 7941227987487264489408877)
                  ·
                    refine ⟨2977960495307724183528329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7941227987487264489408877 2977960495307724183528329)
                    ·
                      refine ⟨2233470371480793137646247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2977960495307724183528329 2233470371480793137646247)
                      ·
                        rfl

theorem cell23_4349668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_4349668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349668 prefixEnd_4349668 := by exact prefixLift 4349668
  have htrace : WordTrace (prefixWord ++ tailWord_4349668) baseStart_4349668 baseEnd_4349668 := by
    simpa [prefixWord, tailWord_4349668, baseEnd_4349668] using wordTrace_append hprefix tailTrace_4349668
  have hstable : (prefixWord ++ tailWord_4349668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349668).length < 2 ^ (prefixWord ++ tailWord_4349668).sum := by decide
  have hdescent : baseEnd_4349668 < baseStart_4349668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349691 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 4, 4]
def baseStart_4349691 : Nat := 118140960795 + 4349691 * 2 ^ 59
def prefixEnd_4349691 : Nat := 4983230072969 + 3 ^ 40 * 4349691 * 2
def baseEnd_4349691 : Nat := 744494060511948849219547

theorem tailTrace_4349691 : CollatzResearch.WordTrace tailWord_4349691 prefixEnd_4349691 744494060511948849219547 := by
  unfold tailWord_4349691
  simp only [CollatzResearch.WordTrace]
  refine ⟨158646264084819849925160927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105764176056546566616773951 158646264084819849925160927)
  ·
    refine ⟨237969396127229774887741391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158646264084819849925160927 237969396127229774887741391)
    ·
      refine ⟨356954094190844662331612087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237969396127229774887741391 356954094190844662331612087)
      ·
        refine ⟨535431141286266993497418131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356954094190844662331612087 535431141286266993497418131)
        ·
          refine ⟨803146711929400490246127197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535431141286266993497418131 803146711929400490246127197)
          ·
            refine ⟨301180016973525183842297699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 803146711929400490246127197 301180016973525183842297699)
            ·
              refine ⟨451770025460287775763446549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301180016973525183842297699 451770025460287775763446549)
              ·
                refine ⟨21176719943450989488911557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 451770025460287775763446549 21176719943450989488911557)
                ·
                  refine ⟨3970634989397060529170917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21176719943450989488911557 3970634989397060529170917)
                  ·
                    refine ⟨744494060511948849219547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970634989397060529170917 744494060511948849219547)
                    ·
                      rfl

theorem cell23_4349691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 4].length) (baseStart_4349691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349691 prefixEnd_4349691 := by exact prefixLift 4349691
  have htrace : WordTrace (prefixWord ++ tailWord_4349691) baseStart_4349691 baseEnd_4349691 := by
    simpa [prefixWord, tailWord_4349691, baseEnd_4349691] using wordTrace_append hprefix tailTrace_4349691
  have hstable : (prefixWord ++ tailWord_4349691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349691).length < 2 ^ (prefixWord ++ tailWord_4349691).sum := by decide
  have hdescent : baseEnd_4349691 < baseStart_4349691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349708 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_4349708 : Nat := 118140960795 + 4349708 * 2 ^ 59
def prefixEnd_4349708 : Nat := 4983230072969 + 3 ^ 40 * 4349708 * 2
def baseEnd_4349708 : Nat := 744496970235657660382021

theorem tailTrace_4349708 : CollatzResearch.WordTrace tailWord_4349708 prefixEnd_4349708 744496970235657660382021 := by
  unfold tailWord_4349708
  simp only [CollatzResearch.WordTrace]
  refine ⟨79323442062879130914264889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105764589417172174552353185 79323442062879130914264889)
  ·
    refine ⟨59492581547159348185698667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79323442062879130914264889 59492581547159348185698667)
    ·
      refine ⟨89238872320739022278548001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59492581547159348185698667 89238872320739022278548001)
      ·
        refine ⟨66929154240554266708911001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89238872320739022278548001 66929154240554266708911001)
        ·
          refine ⟨50196865680415700031683251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66929154240554266708911001 50196865680415700031683251)
          ·
            refine ⟨75295298520623550047524877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50196865680415700031683251 75295298520623550047524877)
            ·
              refine ⟨28235736945233831267821829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75295298520623550047524877 28235736945233831267821829)
              ·
                refine ⟨5294200677231343362716593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28235736945233831267821829 5294200677231343362716593)
                ·
                  refine ⟨3970650507923507522037445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294200677231343362716593 3970650507923507522037445)
                  ·
                    refine ⟨744496970235657660382021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970650507923507522037445 744496970235657660382021)
                    ·
                      rfl

theorem cell23_4349708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_4349708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349708 prefixEnd_4349708 := by exact prefixLift 4349708
  have htrace : WordTrace (prefixWord ++ tailWord_4349708) baseStart_4349708 baseEnd_4349708 := by
    simpa [prefixWord, tailWord_4349708, baseEnd_4349708] using wordTrace_append hprefix tailTrace_4349708
  have hstable : (prefixWord ++ tailWord_4349708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349708).length < 2 ^ (prefixWord ++ tailWord_4349708).sum := by decide
  have hdescent : baseEnd_4349708 < baseStart_4349708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349728 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4349728 : Nat := 118140960795 + 4349728 * 2 ^ 59
def prefixEnd_4349728 : Nat := 4983230072969 + 3 ^ 40 * 4349728 * 2
def baseEnd_4349728 : Nat := 2233501180320062902895971

theorem tailTrace_4349728 : CollatzResearch.WordTrace tailWord_4349728 prefixEnd_4349728 2233501180320062902895971 := by
  unfold tailWord_4349728
  simp only [CollatzResearch.WordTrace]
  refine ⟨79323806792842902622128919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105765075723790536829505225 79323806792842902622128919)
  ·
    refine ⟨118985710189264353933193379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79323806792842902622128919 118985710189264353933193379)
    ·
      refine ⟨178478565283896530899790069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118985710189264353933193379 178478565283896530899790069)
      ·
        refine ⟨16732365495365299771855319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178478565283896530899790069 16732365495365299771855319)
        ·
          refine ⟨25098548243047949657782979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16732365495365299771855319 25098548243047949657782979)
          ·
            refine ⟨37647822364571924486674469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25098548243047949657782979 37647822364571924486674469)
            ·
              refine ⟨7058966693357235841251463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37647822364571924486674469 7058966693357235841251463)
              ·
                refine ⟨10588450040035853761877195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7058966693357235841251463 10588450040035853761877195)
                ·
                  refine ⟨15882675060053780642815793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10588450040035853761877195 15882675060053780642815793)
                  ·
                    refine ⟨11912006295040335482111845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15882675060053780642815793 11912006295040335482111845)
                    ·
                      refine ⟨2233501180320062902895971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11912006295040335482111845 2233501180320062902895971)
                      ·
                        rfl

theorem cell23_4349728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4349728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349728 prefixEnd_4349728 := by exact prefixLift 4349728
  have htrace : WordTrace (prefixWord ++ tailWord_4349728) baseStart_4349728 baseEnd_4349728 := by
    simpa [prefixWord, tailWord_4349728, baseEnd_4349728] using wordTrace_append hprefix tailTrace_4349728
  have hstable : (prefixWord ++ tailWord_4349728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349728).length < 2 ^ (prefixWord ++ tailWord_4349728).sum := by decide
  have hdescent : baseEnd_4349728 < baseStart_4349728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349732 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_4349732 : Nat := 118140960795 + 4349732 * 2 ^ 59
def prefixEnd_4349732 : Nat := 4983230072969 + 3 ^ 40 * 4349732 * 2
def baseEnd_4349732 : Nat := 2233503234242680887245953

theorem tailTrace_4349732 : CollatzResearch.WordTrace tailWord_4349732 prefixEnd_4349732 2233503234242680887245953 := by
  unfold tailWord_4349732
  simp only [CollatzResearch.WordTrace]
  refine ⟨79323879738835656963701725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105765172985114209284935633 79323879738835656963701725)
  ·
    refine ⟨29746454902063371361388147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79323879738835656963701725 29746454902063371361388147)
    ·
      refine ⟨44619682353095057042082221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29746454902063371361388147 44619682353095057042082221)
      ·
        refine ⟨16732380882410646390780833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44619682353095057042082221 16732380882410646390780833)
        ·
          refine ⟨12549285661807984793085625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16732380882410646390780833 12549285661807984793085625)
          ·
            refine ⟨9411964246355988594814219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12549285661807984793085625 9411964246355988594814219)
            ·
              refine ⟨14117946369533982892221329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9411964246355988594814219 14117946369533982892221329)
              ·
                refine ⟨10588459777150487169165997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14117946369533982892221329 10588459777150487169165997)
                ·
                  refine ⟨3970672416431432688437249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10588459777150487169165997 3970672416431432688437249)
                  ·
                    refine ⟨2978004312323574516327937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970672416431432688437249 2978004312323574516327937)
                    ·
                      refine ⟨2233503234242680887245953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978004312323574516327937 2233503234242680887245953)
                      ·
                        rfl

theorem cell23_4349732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_4349732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349732 prefixEnd_4349732 := by exact prefixLift 4349732
  have htrace : WordTrace (prefixWord ++ tailWord_4349732) baseStart_4349732 baseEnd_4349732 := by
    simpa [prefixWord, tailWord_4349732, baseEnd_4349732] using wordTrace_append hprefix tailTrace_4349732
  have hstable : (prefixWord ++ tailWord_4349732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349732).length < 2 ^ (prefixWord ++ tailWord_4349732).sum := by decide
  have hdescent : baseEnd_4349732 < baseStart_4349732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349749 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_4349749 : Nat := 118140960795 + 4349749 * 2 ^ 59
def prefixEnd_4349749 : Nat := 4983230072969 + 3 ^ 40 * 4349749 * 2
def baseEnd_4349749 : Nat := 2233511963413807320733375

theorem tailTrace_4349749 : CollatzResearch.WordTrace tailWord_4349749 prefixEnd_4349749 2233511963413807320733375 := by
  unfold tailWord_4349749
  simp only [CollatzResearch.WordTrace]
  refine ⟨158648379518609725830772301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105765586345739817220514867 158648379518609725830772301)
  ·
    refine ⟨59493142319478647186539613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158648379518609725830772301 59493142319478647186539613)
    ·
      refine ⟨22309928369804492694952355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59493142319478647186539613 22309928369804492694952355)
      ·
        refine ⟨33464892554706739042428533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22309928369804492694952355 33464892554706739042428533)
        ·
          refine ⟨3137333677003756785227675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33464892554706739042428533 3137333677003756785227675)
          ·
            refine ⟨4706000515505635177841513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137333677003756785227675 4706000515505635177841513)
            ·
              refine ⟨3529500386629226383381135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4706000515505635177841513 3529500386629226383381135)
              ·
                refine ⟨5294250579943839575071703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529500386629226383381135 5294250579943839575071703)
                ·
                  refine ⟨7941375869915759362607555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5294250579943839575071703 7941375869915759362607555)
                  ·
                    refine ⟨11912063804873639043911333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7941375869915759362607555 11912063804873639043911333)
                    ·
                      refine ⟨2233511963413807320733375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11912063804873639043911333 2233511963413807320733375)
                      ·
                        rfl

theorem cell23_4349749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_4349749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349749 prefixEnd_4349749 := by exact prefixLift 4349749
  have htrace : WordTrace (prefixWord ++ tailWord_4349749) baseStart_4349749 baseEnd_4349749 := by
    simpa [prefixWord, tailWord_4349749, baseEnd_4349749] using wordTrace_append hprefix tailTrace_4349749
  have hstable : (prefixWord ++ tailWord_4349749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349749).length < 2 ^ (prefixWord ++ tailWord_4349749).sum := by decide
  have hdescent : baseEnd_4349749 < baseStart_4349749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349752 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 1, 2, 3]
def baseStart_4349752 : Nat := 118140960795 + 4349752 * 2 ^ 59
def prefixEnd_4349752 : Nat := 4983230072969 + 3 ^ 40 * 4349752 * 2
def baseEnd_4349752 : Nat := 2233513503855770808995861

theorem tailTrace_4349752 : CollatzResearch.WordTrace tailWord_4349752 prefixEnd_4349752 2233513503855770808995861 := by
  unfold tailWord_4349752
  simp only [CollatzResearch.WordTrace]
  refine ⟨79324244468799428671565755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105765659291732571562087673 79324244468799428671565755)
  ·
    refine ⟨118986366703199143007348633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79324244468799428671565755 118986366703199143007348633)
    ·
      refine ⟨89239775027399357255511475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118986366703199143007348633 89239775027399357255511475)
      ·
        refine ⟨133859662541099035883267213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89239775027399357255511475 133859662541099035883267213)
        ·
          refine ⟨50197373452912138456225205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133859662541099035883267213 50197373452912138456225205)
          ·
            refine ⟨4706003761210512980271113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50197373452912138456225205 4706003761210512980271113)
            ·
              refine ⟨3529502820907884735203335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4706003761210512980271113 3529502820907884735203335)
              ·
                refine ⟨5294254231361827102805003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529502820907884735203335 5294254231361827102805003)
                ·
                  refine ⟨7941381347042740654207505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5294254231361827102805003 7941381347042740654207505)
                  ·
                    refine ⟨5956036010282055490655629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7941381347042740654207505 5956036010282055490655629)
                    ·
                      refine ⟨2233513503855770808995861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5956036010282055490655629 2233513503855770808995861)
                      ·
                        rfl

theorem cell23_4349752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_4349752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349752 prefixEnd_4349752 := by exact prefixLift 4349752
  have htrace : WordTrace (prefixWord ++ tailWord_4349752) baseStart_4349752 baseEnd_4349752 := by
    simpa [prefixWord, tailWord_4349752, baseEnd_4349752] using wordTrace_append hprefix tailTrace_4349752
  have hstable : (prefixWord ++ tailWord_4349752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349752).length < 2 ^ (prefixWord ++ tailWord_4349752).sum := by decide
  have hdescent : baseEnd_4349752 < baseStart_4349752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349766 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4349766 : Nat := 118140960795 + 4349766 * 2 ^ 59
def prefixEnd_4349766 : Nat := 4983230072969 + 3 ^ 40 * 4349766 * 2
def baseEnd_4349766 : Nat := 2233520692584933754220797

theorem tailTrace_4349766 : CollatzResearch.WordTrace tailWord_4349766 prefixEnd_4349766 2233520692584933754220797 := by
  unfold tailWord_4349766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957781236235879304191911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105765999706365425156094101 4957781236235879304191911)
  ·
    refine ⟨7436671854353818956287867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4957781236235879304191911 7436671854353818956287867)
    ·
      refine ⟨11155007781530728434431801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7436671854353818956287867 11155007781530728434431801)
      ·
        refine ⟨8366255836148046325823851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11155007781530728434431801 8366255836148046325823851)
        ·
          refine ⟨12549383754222069488735777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366255836148046325823851 12549383754222069488735777)
          ·
            refine ⟨9412037815666552116551833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12549383754222069488735777 9412037815666552116551833)
            ·
              refine ⟨7059028361749914087413875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9412037815666552116551833 7059028361749914087413875)
              ·
                refine ⟨10588542542624871131120813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7059028361749914087413875 10588542542624871131120813)
                ·
                  refine ⟨3970703453484326674170305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10588542542624871131120813 3970703453484326674170305)
                  ·
                    refine ⟨2978027590113245005627729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970703453484326674170305 2978027590113245005627729)
                    ·
                      refine ⟨2233520692584933754220797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978027590113245005627729 2233520692584933754220797)
                      ·
                        rfl

theorem cell23_4349766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4349766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349766 prefixEnd_4349766 := by exact prefixLift 4349766
  have htrace : WordTrace (prefixWord ++ tailWord_4349766) baseStart_4349766 baseEnd_4349766 := by
    simpa [prefixWord, tailWord_4349766, baseEnd_4349766] using wordTrace_append hprefix tailTrace_4349766
  have hstable : (prefixWord ++ tailWord_4349766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349766).length < 2 ^ (prefixWord ++ tailWord_4349766).sum := by decide
  have hdescent : baseEnd_4349766 < baseStart_4349766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349792 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 1, 3, 2]
def baseStart_4349792 : Nat := 118140960795 + 4349792 * 2 ^ 59
def prefixEnd_4349792 : Nat := 4983230072969 + 3 ^ 40 * 4349792 * 2
def baseEnd_4349792 : Nat := 2233534043081950652495677

theorem tailTrace_4349792 : CollatzResearch.WordTrace tailWord_4349792 prefixEnd_4349792 2233534043081950652495677 := by
  unfold tailWord_4349792
  simp only [CollatzResearch.WordTrace]
  refine ⟨79324973928726972087293815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105766631904969296116391753 79324973928726972087293815)
  ·
    refine ⟨118987460893090458130940723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79324973928726972087293815 118987460893090458130940723)
    ·
      refine ⟨178481191339635687196411085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118987460893090458130940723 178481191339635687196411085)
      ·
        refine ⟨66930446752363382698654157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178481191339635687196411085 66930446752363382698654157)
        ·
          refine ⟨25098917532136268511995309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66930446752363382698654157 25098917532136268511995309)
          ·
            refine ⟨9412094074551100691998241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25098917532136268511995309 9412094074551100691998241)
            ·
              refine ⟨7059070555913325518998681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9412094074551100691998241 7059070555913325518998681)
              ·
                refine ⟨5294302916934994139249011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7059070555913325518998681 5294302916934994139249011)
                ·
                  refine ⟨7941454375402491208873517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5294302916934994139249011 7941454375402491208873517)
                  ·
                    refine ⟨2978045390775934203327569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7941454375402491208873517 2978045390775934203327569)
                    ·
                      refine ⟨2233534043081950652495677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978045390775934203327569 2233534043081950652495677)
                      ·
                        rfl

theorem cell23_4349792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_4349792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349792 prefixEnd_4349792 := by exact prefixLift 4349792
  have htrace : WordTrace (prefixWord ++ tailWord_4349792) baseStart_4349792 baseEnd_4349792 := by
    simpa [prefixWord, tailWord_4349792, baseEnd_4349792] using wordTrace_append hprefix tailTrace_4349792
  have hstable : (prefixWord ++ tailWord_4349792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349792).length < 2 ^ (prefixWord ++ tailWord_4349792).sum := by decide
  have hdescent : baseEnd_4349792 < baseStart_4349792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349801 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_4349801 : Nat := 118140960795 + 4349801 * 2 ^ 59
def prefixEnd_4349801 : Nat := 4983230072969 + 3 ^ 40 * 4349801 * 2
def baseEnd_4349801 : Nat := 2233538664407841117283135

theorem tailTrace_4349801 : CollatzResearch.WordTrace tailWord_4349801 prefixEnd_4349801 2233538664407841117283135 := by
  unfold tailWord_4349801
  simp only [CollatzResearch.WordTrace]
  refine ⟨158650276114421338711665257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105766850742947559141110171 158650276114421338711665257)
  ·
    refine ⟨118987707085816004033748943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158650276114421338711665257 118987707085816004033748943)
    ·
      refine ⟨178481560628724006050623415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118987707085816004033748943 178481560628724006050623415)
      ·
        refine ⟨267722340943086009075935123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178481560628724006050623415 267722340943086009075935123)
        ·
          refine ⟨401583511414629013613902685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267722340943086009075935123 401583511414629013613902685)
          ·
            refine ⟨150593816780485880105213507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401583511414629013613902685 150593816780485880105213507)
            ·
              refine ⟨225890725170728820157820261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150593816780485880105213507 225890725170728820157820261)
              ·
                refine ⟨42354510969511653779591299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225890725170728820157820261 42354510969511653779591299)
                ·
                  refine ⟨63531766454267480669386949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42354510969511653779591299 63531766454267480669386949)
                  ·
                    refine ⟨11912206210175152625510053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63531766454267480669386949 11912206210175152625510053)
                    ·
                      refine ⟨2233538664407841117283135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11912206210175152625510053 2233538664407841117283135)
                      ·
                        rfl

theorem cell23_4349801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_4349801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349801 prefixEnd_4349801 := by exact prefixLift 4349801
  have htrace : WordTrace (prefixWord ++ tailWord_4349801) baseStart_4349801 baseEnd_4349801 := by
    simpa [prefixWord, tailWord_4349801, baseEnd_4349801] using wordTrace_append hprefix tailTrace_4349801
  have hstable : (prefixWord ++ tailWord_4349801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349801).length < 2 ^ (prefixWord ++ tailWord_4349801).sum := by decide
  have hdescent : baseEnd_4349801 < baseStart_4349801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349805 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_4349805 : Nat := 118140960795 + 4349805 * 2 ^ 59
def prefixEnd_4349805 : Nat := 4983230072969 + 3 ^ 40 * 4349805 * 2
def baseEnd_4349805 : Nat := 2233540718330459101633117

theorem tailTrace_4349805 : CollatzResearch.WordTrace tailWord_4349805 prefixEnd_4349805 2233540718330459101633117 := by
  unfold tailWord_4349805
  simp only [CollatzResearch.WordTrace]
  refine ⟨158650422006406847394810869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105766948004271231596540579 158650422006406847394810869)
  ·
    refine ⟨14873477063100641943263519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158650422006406847394810869 14873477063100641943263519)
    ·
      refine ⟨22310215594650962914895279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14873477063100641943263519 22310215594650962914895279)
      ·
        refine ⟨33465323391976444372342919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22310215594650962914895279 33465323391976444372342919)
        ·
          refine ⟨50197985087964666558514379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33465323391976444372342919 50197985087964666558514379)
          ·
            refine ⟨75296977631946999837771569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50197985087964666558514379 75296977631946999837771569)
            ·
              refine ⟨56472733223960249878328677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75296977631946999837771569 56472733223960249878328677)
              ·
                refine ⟨10588637479492546852186627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56472733223960249878328677 10588637479492546852186627)
                ·
                  refine ⟨15882956219238820278279941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10588637479492546852186627 15882956219238820278279941)
                  ·
                    refine ⟨2978054291107278802177489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15882956219238820278279941 2978054291107278802177489)
                    ·
                      refine ⟨2233540718330459101633117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978054291107278802177489 2233540718330459101633117)
                      ·
                        rfl

theorem cell23_4349805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_4349805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349805 prefixEnd_4349805 := by exact prefixLift 4349805
  have htrace : WordTrace (prefixWord ++ tailWord_4349805) baseStart_4349805 baseEnd_4349805 := by
    simpa [prefixWord, tailWord_4349805, baseEnd_4349805] using wordTrace_append hprefix tailTrace_4349805
  have hstable : (prefixWord ++ tailWord_4349805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349805).length < 2 ^ (prefixWord ++ tailWord_4349805).sum := by decide
  have hdescent : baseEnd_4349805 < baseStart_4349805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349821 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_4349821 : Nat := 118140960795 + 4349821 * 2 ^ 59
def prefixEnd_4349821 : Nat := 4983230072969 + 3 ^ 40 * 4349821 * 2
def baseEnd_4349821 : Nat := 2233548934020931039033043

theorem tailTrace_4349821 : CollatzResearch.WordTrace tailWord_4349821 prefixEnd_4349821 2233548934020931039033043 := by
  unfold tailWord_4349821
  simp only [CollatzResearch.WordTrace]
  refine ⟨158651005574348882127393317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105767337049565921418262211 158651005574348882127393317)
  ·
    refine ⟨29747063545190415398886247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158651005574348882127393317 29747063545190415398886247)
    ·
      refine ⟨44620595317785623098329371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29747063545190415398886247 44620595317785623098329371)
      ·
        refine ⟨66930892976678434647494057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44620595317785623098329371 66930892976678434647494057)
        ·
          refine ⟨50198169732508825985620543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66930892976678434647494057 50198169732508825985620543)
          ·
            refine ⟨75297254598763238978430815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50198169732508825985620543 75297254598763238978430815)
            ·
              refine ⟨112945881898144858467646223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75297254598763238978430815 112945881898144858467646223)
              ·
                refine ⟨169418822847217287701469335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112945881898144858467646223 169418822847217287701469335)
                ·
                  refine ⟨254128234270825931552204003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169418822847217287701469335 254128234270825931552204003)
                  ·
                    refine ⟨381192351406238897328306005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 254128234270825931552204003 381192351406238897328306005)
                    ·
                      refine ⟨2233548934020931039033043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 381192351406238897328306005 2233548934020931039033043)
                      ·
                        rfl

theorem cell23_4349821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_4349821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349821 prefixEnd_4349821 := by exact prefixLift 4349821
  have htrace : WordTrace (prefixWord ++ tailWord_4349821) baseStart_4349821 baseEnd_4349821 := by
    simpa [prefixWord, tailWord_4349821, baseEnd_4349821] using wordTrace_append hprefix tailTrace_4349821
  have hstable : (prefixWord ++ tailWord_4349821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349821).length < 2 ^ (prefixWord ++ tailWord_4349821).sum := by decide
  have hdescent : baseEnd_4349821 < baseStart_4349821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349828 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 7]
def baseStart_4349828 : Nat := 118140960795 + 4349828 * 2 ^ 59
def prefixEnd_4349828 : Nat := 4983230072969 + 3 ^ 40 * 4349828 * 2
def baseEnd_4349828 : Nat := 248172503153945834627279

theorem tailTrace_4349828 : CollatzResearch.WordTrace tailWord_4349828 prefixEnd_4349828 248172503153945834627279 := by
  unfold tailWord_4349828
  simp only [CollatzResearch.WordTrace]
  refine ⟨79325630442661761161449069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105767507256882348215265425 79325630442661761161449069)
  ·
    refine ⟨29747111415998160435543401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79325630442661761161449069 29747111415998160435543401)
    ·
      refine ⟨22310333561998620326657551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29747111415998160435543401 22310333561998620326657551)
      ·
        refine ⟨33465500342997930489986327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22310333561998620326657551 33465500342997930489986327)
        ·
          refine ⟨50198250514496895734979491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33465500342997930489986327 50198250514496895734979491)
          ·
            refine ⟨75297375771745343602469237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50198250514496895734979491 75297375771745343602469237)
            ·
              refine ⟨7059128978601125962731491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75297375771745343602469237 7059128978601125962731491)
              ·
                refine ⟨10588693467901688944097237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7059128978601125962731491 10588693467901688944097237)
                ·
                  refine ⟨248172503153945834627279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10588693467901688944097237 248172503153945834627279)
                  ·
                    rfl

theorem cell23_4349828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_4349828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349828 prefixEnd_4349828 := by exact prefixLift 4349828
  have htrace : WordTrace (prefixWord ++ tailWord_4349828) baseStart_4349828 baseEnd_4349828 := by
    simpa [prefixWord, tailWord_4349828, baseEnd_4349828] using wordTrace_append hprefix tailTrace_4349828
  have hstable : (prefixWord ++ tailWord_4349828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349828).length < 2 ^ (prefixWord ++ tailWord_4349828).sum := by decide
  have hdescent : baseEnd_4349828 < baseStart_4349828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4349841 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_4349841 : Nat := 118140960795 + 4349841 * 2 ^ 59
def prefixEnd_4349841 : Nat := 4983230072969 + 3 ^ 40 * 4349841 * 2
def baseEnd_4349841 : Nat := 744519734544673653594317

theorem tailTrace_4349841 : CollatzResearch.WordTrace tailWord_4349841 prefixEnd_4349841 744519734544673653594317 := by
  unfold tailWord_4349841
  simp only [CollatzResearch.WordTrace]
  refine ⟨158651735034276425543121377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105767823356184283695414251 158651735034276425543121377)
  ·
    refine ⟨118988801275707319157341033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158651735034276425543121377 118988801275707319157341033)
    ·
      refine ⟨89241600956780489368005775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118988801275707319157341033 89241600956780489368005775)
      ·
        refine ⟨133862401435170734052008663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89241600956780489368005775 133862401435170734052008663)
        ·
          refine ⟨200793602152756101078012995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133862401435170734052008663 200793602152756101078012995)
          ·
            refine ⟨301190403229134151617019493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200793602152756101078012995 301190403229134151617019493)
            ·
              refine ⟨56473200605462653428191155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301190403229134151617019493 56473200605462653428191155)
              ·
                refine ⟨84709800908193980142286733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56473200605462653428191155 84709800908193980142286733)
                ·
                  refine ⟨31766175340572742553357525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84709800908193980142286733 31766175340572742553357525)
                  ·
                    refine ⟨744519734544673653594317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31766175340572742553357525 744519734544673653594317)
                    ·
                      rfl

theorem cell23_4349841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_4349841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4349841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4349841 prefixEnd_4349841 := by exact prefixLift 4349841
  have htrace : WordTrace (prefixWord ++ tailWord_4349841) baseStart_4349841 baseEnd_4349841 := by
    simpa [prefixWord, tailWord_4349841, baseEnd_4349841] using wordTrace_append hprefix tailTrace_4349841
  have hstable : (prefixWord ++ tailWord_4349841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4349841).length < 2 ^ (prefixWord ++ tailWord_4349841).sum := by decide
  have hdescent : baseEnd_4349841 < baseStart_4349841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4349841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350005 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4350005 : Nat := 118140960795 + 4350005 * 2 ^ 59
def prefixEnd_4350005 : Nat := 4983230072969 + 3 ^ 40 * 4350005 * 2
def baseEnd_4350005 : Nat := 2233643414461358319132197

theorem tailTrace_4350005 : CollatzResearch.WordTrace tailWord_4350005 prefixEnd_4350005 2233643414461358319132197 := by
  unfold tailWord_4350005
  simp only [CollatzResearch.WordTrace]
  refine ⟨158657716605682281552091469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105771811070454854368060979 158657716605682281552091469)
  ·
    refine ⟨59496643727130855582034301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158657716605682281552091469 59496643727130855582034301)
    ·
      refine ⟨22311241397674070843262863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59496643727130855582034301 22311241397674070843262863)
      ·
        refine ⟨33466862096511106264894295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22311241397674070843262863 33466862096511106264894295)
        ·
          refine ⟨50200293144766659397341443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33466862096511106264894295 50200293144766659397341443)
          ·
            refine ⟨75300439717149989096012165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50200293144766659397341443 75300439717149989096012165)
            ·
              refine ⟨14118832446965622955502281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75300439717149989096012165 14118832446965622955502281)
              ·
                refine ⟨10589124335224217216626711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14118832446965622955502281 10589124335224217216626711)
                ·
                  refine ⟨15883686502836325824940067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10589124335224217216626711 15883686502836325824940067)
                  ·
                    refine ⟨23825529754254488737410101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15883686502836325824940067 23825529754254488737410101)
                    ·
                      refine ⟨2233643414461358319132197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23825529754254488737410101 2233643414461358319132197)
                      ·
                        rfl

theorem cell23_4350005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4350005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350005 prefixEnd_4350005 := by exact prefixLift 4350005
  have htrace : WordTrace (prefixWord ++ tailWord_4350005) baseStart_4350005 baseEnd_4350005 := by
    simpa [prefixWord, tailWord_4350005, baseEnd_4350005] using wordTrace_append hprefix tailTrace_4350005
  have hstable : (prefixWord ++ tailWord_4350005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350005).length < 2 ^ (prefixWord ++ tailWord_4350005).sum := by decide
  have hdescent : baseEnd_4350005 < baseStart_4350005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350012 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_4350012 : Nat := 118140960795 + 4350012 * 2 ^ 59
def prefixEnd_4350012 : Nat := 4983230072969 + 3 ^ 40 * 4350012 * 2
def baseEnd_4350012 : Nat := 744549002941979930581555

theorem tailTrace_4350012 : CollatzResearch.WordTrace tailWord_4350012 prefixEnd_4350012 744549002941979930581555 := by
  unfold tailWord_4350012
  simp only [CollatzResearch.WordTrace]
  refine ⟨79328985958328460873798145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105771981277771281165064193 79328985958328460873798145)
  ·
    refine ⟨59496739468746345655348609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79328985958328460873798145 59496739468746345655348609)
    ·
      refine ⟨44622554601559759241511457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59496739468746345655348609 44622554601559759241511457)
      ·
        refine ⟨33466915951169819431133593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44622554601559759241511457 33466915951169819431133593)
        ·
          refine ⟨25100186963377364573350195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33466915951169819431133593 25100186963377364573350195)
          ·
            refine ⟨37650280445066046860025293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25100186963377364573350195 37650280445066046860025293)
            ·
              refine ⟨14118855166899767572509485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37650280445066046860025293 14118855166899767572509485)
              ·
                refine ⟨5294570687587412839691057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14118855166899767572509485 5294570687587412839691057)
                ·
                  refine ⟨3970928015690559629768293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294570687587412839691057 3970928015690559629768293)
                  ·
                    refine ⟨744549002941979930581555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970928015690559629768293 744549002941979930581555)
                    ·
                      rfl

theorem cell23_4350012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_4350012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350012 prefixEnd_4350012 := by exact prefixLift 4350012
  have htrace : WordTrace (prefixWord ++ tailWord_4350012) baseStart_4350012 baseEnd_4350012 := by
    simpa [prefixWord, tailWord_4350012, baseEnd_4350012] using wordTrace_append hprefix tailTrace_4350012
  have hstable : (prefixWord ++ tailWord_4350012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350012).length < 2 ^ (prefixWord ++ tailWord_4350012).sum := by decide
  have hdescent : baseEnd_4350012 < baseStart_4350012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350036 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_4350036 : Nat := 118140960795 + 4350036 * 2 ^ 59
def prefixEnd_4350036 : Nat := 4983230072969 + 3 ^ 40 * 4350036 * 2
def baseEnd_4350036 : Nat := 2233659332361647697844555

theorem tailTrace_4350036 : CollatzResearch.WordTrace tailWord_4350036 prefixEnd_4350036 2233659332361647697844555 := by
  unfold tailWord_4350036
  simp only [CollatzResearch.WordTrace]
  refine ⟨79329423634284986923234981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105772564845713315897646641 79329423634284986923234981)
  ·
    refine ⟨14874266931428435048106559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79329423634284986923234981 14874266931428435048106559)
    ·
      refine ⟨22311400397142652572159839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14874266931428435048106559 22311400397142652572159839)
      ·
        refine ⟨33467100595713978858239759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22311400397142652572159839 33467100595713978858239759)
        ·
          refine ⟨50200650893570968287359639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33467100595713978858239759 50200650893570968287359639)
          ·
            refine ⟨75300976340356452431039459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50200650893570968287359639 75300976340356452431039459)
            ·
              refine ⟨112951464510534678646559189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75300976340356452431039459 112951464510534678646559189)
              ·
                refine ⟨2647299949465656530778731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112951464510534678646559189 2647299949465656530778731)
                ·
                  refine ⟨3970949924198484796168097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647299949465656530778731 3970949924198484796168097)
                  ·
                    refine ⟨2978212443148863597126073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970949924198484796168097 2978212443148863597126073)
                    ·
                      refine ⟨2233659332361647697844555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978212443148863597126073 2233659332361647697844555)
                      ·
                        rfl

theorem cell23_4350036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_4350036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350036 prefixEnd_4350036 := by exact prefixLift 4350036
  have htrace : WordTrace (prefixWord ++ tailWord_4350036) baseStart_4350036 baseEnd_4350036 := by
    simpa [prefixWord, tailWord_4350036, baseEnd_4350036] using wordTrace_append hprefix tailTrace_4350036
  have hstable : (prefixWord ++ tailWord_4350036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350036).length < 2 ^ (prefixWord ++ tailWord_4350036).sum := by decide
  have hdescent : baseEnd_4350036 < baseStart_4350036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350052 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_4350052 : Nat := 118140960795 + 4350052 * 2 ^ 59
def prefixEnd_4350052 : Nat := 4983230072969 + 3 ^ 40 * 4350052 * 2
def baseEnd_4350052 : Nat := 2233667548052119635244481

theorem tailTrace_4350052 : CollatzResearch.WordTrace tailWord_4350052 prefixEnd_4350052 2233667548052119635244481 := by
  unfold tailWord_4350052
  simp only [CollatzResearch.WordTrace]
  refine ⟨79329715418256004289526205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105772953891008005719368273 79329715418256004289526205)
  ·
    refine ⟨29748643281846001608572327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79329715418256004289526205 29748643281846001608572327)
    ·
      refine ⟨44622964922769002412858491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29748643281846001608572327 44622964922769002412858491)
      ·
        refine ⟨66934447384153503619287737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44622964922769002412858491 66934447384153503619287737)
        ·
          refine ⟨50200835538115127714465803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66934447384153503619287737 50200835538115127714465803)
          ·
            refine ⟨75301253307172691571698705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50200835538115127714465803 75301253307172691571698705)
            ·
              refine ⟨56475939980379518678774029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75301253307172691571698705 56475939980379518678774029)
              ·
                refine ⟨21178477492642319504540261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56475939980379518678774029 21178477492642319504540261)
                ·
                  refine ⟨3970964529870434907101299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21178477492642319504540261 3970964529870434907101299)
                  ·
                    refine ⟨5956446794805652360651949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3970964529870434907101299 5956446794805652360651949)
                    ·
                      refine ⟨2233667548052119635244481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5956446794805652360651949 2233667548052119635244481)
                      ·
                        rfl

theorem cell23_4350052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_4350052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350052 prefixEnd_4350052 := by exact prefixLift 4350052
  have htrace : WordTrace (prefixWord ++ tailWord_4350052) baseStart_4350052 baseEnd_4350052 := by
    simpa [prefixWord, tailWord_4350052, baseEnd_4350052] using wordTrace_append hprefix tailTrace_4350052
  have hstable : (prefixWord ++ tailWord_4350052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350052).length < 2 ^ (prefixWord ++ tailWord_4350052).sum := by decide
  have hdescent : baseEnd_4350052 < baseStart_4350052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350053 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 1, 2, 2]
def baseStart_4350053 : Nat := 118140960795 + 4350053 * 2 ^ 59
def prefixEnd_4350053 : Nat := 4983230072969 + 3 ^ 40 * 4350053 * 2
def baseEnd_4350053 : Nat := 2233668061532774131331977

theorem tailTrace_4350053 : CollatzResearch.WordTrace tailWord_4350053 prefixEnd_4350053 2233668061532774131331977 := by
  unfold tailWord_4350053
  simp only [CollatzResearch.WordTrace]
  refine ⟨158659467309508385749838813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105772978206338923833225875 158659467309508385749838813)
  ·
    refine ⟨59497300241065644656189555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158659467309508385749838813 59497300241065644656189555)
    ·
      refine ⟨89245950361598466984284333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59497300241065644656189555 89245950361598466984284333)
      ·
        refine ⟨33467231385599425119106625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89245950361598466984284333 33467231385599425119106625)
        ·
          refine ⟨25100423539199568839329969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33467231385599425119106625 25100423539199568839329969)
          ·
            refine ⟨18825317654399676629497477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25100423539199568839329969 18825317654399676629497477)
            ·
              refine ⟨3529747060199939368030777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18825317654399676629497477 3529747060199939368030777)
              ·
                refine ⟨2647310295149954526023083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3529747060199939368030777 2647310295149954526023083)
                ·
                  refine ⟨3970965442724931789034625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647310295149954526023083 3970965442724931789034625)
                  ·
                    refine ⟨2978224082043698841775969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970965442724931789034625 2978224082043698841775969)
                    ·
                      refine ⟨2233668061532774131331977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978224082043698841775969 2233668061532774131331977)
                      ·
                        rfl

theorem cell23_4350053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_4350053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350053 prefixEnd_4350053 := by exact prefixLift 4350053
  have htrace : WordTrace (prefixWord ++ tailWord_4350053) baseStart_4350053 baseEnd_4350053 := by
    simpa [prefixWord, tailWord_4350053, baseEnd_4350053] using wordTrace_append hprefix tailTrace_4350053
  have hstable : (prefixWord ++ tailWord_4350053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350053).length < 2 ^ (prefixWord ++ tailWord_4350053).sum := by decide
  have hdescent : baseEnd_4350053 < baseStart_4350053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350103 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 2, 1, 3]
def baseStart_4350103 : Nat := 118140960795 + 4350103 * 2 ^ 59
def prefixEnd_4350103 : Nat := 4983230072969 + 3 ^ 40 * 4350103 * 2
def baseEnd_4350103 : Nat := 2233693735565498935706747

theorem tailTrace_4350103 : CollatzResearch.WordTrace tailWord_4350103 prefixEnd_4350103 2233693735565498935706747 := by
  unfold tailWord_4350103
  simp only [CollatzResearch.WordTrace]
  refine ⟨158661290959327244289158963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105774193972884829526105975 158661290959327244289158963)
  ·
    refine ⟨237991936438990866433738445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158661290959327244289158963 237991936438990866433738445)
    ·
      refine ⟨89246976164621574912651917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237991936438990866433738445 89246976164621574912651917)
      ·
        refine ⟨33467616061733090592244469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89246976164621574912651917 33467616061733090592244469)
        ·
          refine ⟨3137589005787477243022919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33467616061733090592244469 3137589005787477243022919)
          ·
            refine ⟨4706383508681215864534379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137589005787477243022919 4706383508681215864534379)
            ·
              refine ⟨7059575263021823796801569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706383508681215864534379 7059575263021823796801569)
              ·
                refine ⟨5294681447266367847601177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7059575263021823796801569 5294681447266367847601177)
                ·
                  refine ⟨3971011085449775885700883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294681447266367847601177 3971011085449775885700883)
                  ·
                    refine ⟨5956516628174663828551325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3971011085449775885700883 5956516628174663828551325)
                    ·
                      refine ⟨2233693735565498935706747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5956516628174663828551325 2233693735565498935706747)
                      ·
                        rfl

theorem cell23_4350103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_4350103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350103 prefixEnd_4350103 := by exact prefixLift 4350103
  have htrace : WordTrace (prefixWord ++ tailWord_4350103) baseStart_4350103 baseEnd_4350103 := by
    simpa [prefixWord, tailWord_4350103, baseEnd_4350103] using wordTrace_append hprefix tailTrace_4350103
  have hstable : (prefixWord ++ tailWord_4350103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350103).length < 2 ^ (prefixWord ++ tailWord_4350103).sum := by decide
  have hdescent : baseEnd_4350103 < baseStart_4350103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350146 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4350146 : Nat := 118140960795 + 4350146 * 2 ^ 59
def prefixEnd_4350146 : Nat := 4983230072969 + 3 ^ 40 * 4350146 * 2
def baseEnd_4350146 : Nat := 2233715815233642267469049

theorem tailTrace_4350146 : CollatzResearch.WordTrace tailWord_4350146 prefixEnd_4350146 2233715815233642267469049 := by
  unfold tailWord_4350146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39665714824542865658243573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105775239532114308421982861 39665714824542865658243573)
  ·
    refine ⟨3718660764800893655460335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39665714824542865658243573 3718660764800893655460335)
    ·
      refine ⟨5577991147201340483190503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718660764800893655460335 5577991147201340483190503)
      ·
        refine ⟨8366986720802010724785755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577991147201340483190503 8366986720802010724785755)
        ·
          refine ⟨12550480081203016087178633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366986720802010724785755 12550480081203016087178633)
          ·
            refine ⟨9412860060902262065383975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12550480081203016087178633 9412860060902262065383975)
            ·
              refine ⟨14119290091353393098075963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9412860060902262065383975 14119290091353393098075963)
              ·
                refine ⟨21178935137030089647113945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14119290091353393098075963 21178935137030089647113945)
                ·
                  refine ⟨15884201352772567235335459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21178935137030089647113945 15884201352772567235335459)
                  ·
                    refine ⟨23826302029158850853003189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15884201352772567235335459 23826302029158850853003189)
                    ·
                      refine ⟨2233715815233642267469049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23826302029158850853003189 2233715815233642267469049)
                      ·
                        rfl

theorem cell23_4350146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4350146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350146 prefixEnd_4350146 := by exact prefixLift 4350146
  have htrace : WordTrace (prefixWord ++ tailWord_4350146) baseStart_4350146 baseEnd_4350146 := by
    simpa [prefixWord, tailWord_4350146, baseEnd_4350146] using wordTrace_append hprefix tailTrace_4350146
  have hstable : (prefixWord ++ tailWord_4350146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350146).length < 2 ^ (prefixWord ++ tailWord_4350146).sum := by decide
  have hdescent : baseEnd_4350146 < baseStart_4350146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350152 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_4350152 : Nat := 118140960795 + 4350152 * 2 ^ 59
def prefixEnd_4350152 : Nat := 4983230072969 + 3 ^ 40 * 4350152 * 2
def baseEnd_4350152 : Nat := 2233718896117569243994021

theorem tailTrace_4350152 : CollatzResearch.WordTrace tailWord_4350152 prefixEnd_4350152 2233718896117569243994021 := by
  unfold tailWord_4350152
  simp only [CollatzResearch.WordTrace]
  refine ⟨79331539068074862828846355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105775385424099817105128473 79331539068074862828846355)
  ·
    refine ⟨118997308602112294243269533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79331539068074862828846355 118997308602112294243269533)
    ·
      refine ⟨44623990725792110341226075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118997308602112294243269533 44623990725792110341226075)
      ·
        refine ⟨66935986088688165511839113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44623990725792110341226075 66935986088688165511839113)
        ·
          refine ⟨50201989566516124133879335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66935986088688165511839113 50201989566516124133879335)
          ·
            refine ⟨75302984349774186200819003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50201989566516124133879335 75302984349774186200819003)
            ·
              refine ⟨112954476524661279301228505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75302984349774186200819003 112954476524661279301228505)
              ·
                refine ⟨84715857393495959475921379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112954476524661279301228505 84715857393495959475921379)
                ·
                  refine ⟨127073786090243939213882069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84715857393495959475921379 127073786090243939213882069)
                  ·
                    refine ⟨2978291861490092325325361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127073786090243939213882069 2978291861490092325325361)
                    ·
                      refine ⟨2233718896117569243994021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978291861490092325325361 2233718896117569243994021)
                      ·
                        rfl

theorem cell23_4350152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_4350152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350152 prefixEnd_4350152 := by exact prefixLift 4350152
  have htrace : WordTrace (prefixWord ++ tailWord_4350152) baseStart_4350152 baseEnd_4350152 := by
    simpa [prefixWord, tailWord_4350152, baseEnd_4350152] using wordTrace_append hprefix tailTrace_4350152
  have hstable : (prefixWord ++ tailWord_4350152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350152).length < 2 ^ (prefixWord ++ tailWord_4350152).sum := by decide
  have hdescent : baseEnd_4350152 < baseStart_4350152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350155 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5]
def baseStart_4350155 : Nat := 118140960795 + 4350155 * 2 ^ 59
def prefixEnd_4350155 : Nat := 4983230072969 + 3 ^ 40 * 4350155 * 2
def baseEnd_4350155 : Nat := 2233720436559532732256507

theorem tailTrace_4350155 : CollatzResearch.WordTrace tailWord_4350155 prefixEnd_4350155 2233720436559532732256507 := by
  unfold tailWord_4350155
  simp only [CollatzResearch.WordTrace]
  refine ⟨158663187555138857170051919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105775458370092571446701279 158663187555138857170051919)
  ·
    refine ⟨237994781332708285755077879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158663187555138857170051919 237994781332708285755077879)
    ·
      refine ⟨356992171999062428632616819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237994781332708285755077879 356992171999062428632616819)
      ·
        refine ⟨535488257998593642948925229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356992171999062428632616819 535488257998593642948925229)
        ·
          refine ⟨200808096749472616105846961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535488257998593642948925229 200808096749472616105846961)
          ·
            refine ⟨150606072562104462079385221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200808096749472616105846961 150606072562104462079385221)
            ·
              refine ⟨28238638605394586639884729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150606072562104462079385221 28238638605394586639884729)
              ·
                refine ⟨21178978954045939979913547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28238638605394586639884729 21178978954045939979913547)
                ·
                  refine ⟨31768468431068909969870321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21178978954045939979913547 31768468431068909969870321)
                  ·
                    refine ⟨23826351323301682477402741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31768468431068909969870321 23826351323301682477402741)
                    ·
                      refine ⟨2233720436559532732256507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23826351323301682477402741 2233720436559532732256507)
                      ·
                        rfl

theorem cell23_4350155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_4350155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350155 prefixEnd_4350155 := by exact prefixLift 4350155
  have htrace : WordTrace (prefixWord ++ tailWord_4350155) baseStart_4350155 baseEnd_4350155 := by
    simpa [prefixWord, tailWord_4350155, baseEnd_4350155] using wordTrace_append hprefix tailTrace_4350155
  have hstable : (prefixWord ++ tailWord_4350155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350155).length < 2 ^ (prefixWord ++ tailWord_4350155).sum := by decide
  have hdescent : baseEnd_4350155 < baseStart_4350155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350162 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_4350162 : Nat := 118140960795 + 4350162 * 2 ^ 59
def prefixEnd_4350162 : Nat := 4983230072969 + 3 ^ 40 * 4350162 * 2
def baseEnd_4350162 : Nat := 744574676974704734956325

theorem tailTrace_4350162 : CollatzResearch.WordTrace tailWord_4350162 prefixEnd_4350162 744574676974704734956325 := by
  unfold tailWord_4350162
  simp only [CollatzResearch.WordTrace]
  refine ⟨39665860716528374341389185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105775628577408998243704493 39665860716528374341389185)
  ·
    refine ⟨29749395537396280756041889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39665860716528374341389185 29749395537396280756041889)
    ·
      refine ⟨22312046653047210567031417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29749395537396280756041889 22312046653047210567031417)
      ·
        refine ⟨16734034989785407925273563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22312046653047210567031417 16734034989785407925273563)
        ·
          refine ⟨25101052484678111887910345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16734034989785407925273563 25101052484678111887910345)
          ·
            refine ⟨18825789363508583915932759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25101052484678111887910345 18825789363508583915932759)
            ·
              refine ⟨28238684045262875873899139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18825789363508583915932759 28238684045262875873899139)
              ·
                refine ⟨42358026067894313810848709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28238684045262875873899139 42358026067894313810848709)
                ·
                  refine ⟨7942129887730183839534133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42358026067894313810848709 7942129887730183839534133)
                  ·
                    refine ⟨744574676974704734956325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7942129887730183839534133 744574676974704734956325)
                    ·
                      rfl

theorem cell23_4350162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_4350162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350162 prefixEnd_4350162 := by exact prefixLift 4350162
  have htrace : WordTrace (prefixWord ++ tailWord_4350162) baseStart_4350162 baseEnd_4350162 := by
    simpa [prefixWord, tailWord_4350162, baseEnd_4350162] using wordTrace_append hprefix tailTrace_4350162
  have hstable : (prefixWord ++ tailWord_4350162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350162).length < 2 ^ (prefixWord ++ tailWord_4350162).sum := by decide
  have hdescent : baseEnd_4350162 < baseStart_4350162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350166 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_4350166 : Nat := 118140960795 + 4350166 * 2 ^ 59
def prefixEnd_4350166 : Nat := 4983230072969 + 3 ^ 40 * 4350166 * 2
def baseEnd_4350166 : Nat := 248191787205192465468773

theorem tailTrace_4350166 : CollatzResearch.WordTrace tailWord_4350166 prefixEnd_4350166 248191787205192465468773 := by
  unfold tailWord_4350166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9916474297381187878043897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105775725838732670699134901 9916474297381187878043897)
  ·
    refine ⟨7437355723035890908532923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9916474297381187878043897 7437355723035890908532923)
    ·
      refine ⟨11156033584553836362799385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7437355723035890908532923 11156033584553836362799385)
      ·
        refine ⟨8367025188415377272099539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11156033584553836362799385 8367025188415377272099539)
        ·
          refine ⟨12550537782623065908149309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367025188415377272099539 12550537782623065908149309)
          ·
            refine ⟨4706451668483649715555991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12550537782623065908149309 4706451668483649715555991)
            ·
              refine ⟨7059677502725474573333987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706451668483649715555991 7059677502725474573333987)
              ·
                refine ⟨10589516254088211860000981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7059677502725474573333987 10589516254088211860000981)
                ·
                  refine ⟨248191787205192465468773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10589516254088211860000981 248191787205192465468773)
                  ·
                    rfl

theorem cell23_4350166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_4350166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350166 prefixEnd_4350166 := by exact prefixLift 4350166
  have htrace : WordTrace (prefixWord ++ tailWord_4350166) baseStart_4350166 baseEnd_4350166 := by
    simpa [prefixWord, tailWord_4350166, baseEnd_4350166] using wordTrace_append hprefix tailTrace_4350166
  have hstable : (prefixWord ++ tailWord_4350166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350166).length < 2 ^ (prefixWord ++ tailWord_4350166).sum := by decide
  have hdescent : baseEnd_4350166 < baseStart_4350166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350192 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 3, 4]
def baseStart_4350192 : Nat := 118140960795 + 4350192 * 2 ^ 59
def prefixEnd_4350192 : Nat := 4983230072969 + 3 ^ 40 * 4350192 * 2
def baseEnd_4350192 : Nat := 744579811781249695831279

theorem tailTrace_4350192 : CollatzResearch.WordTrace tailWord_4350192 prefixEnd_4350192 744579811781249695831279 := by
  unfold tailWord_4350192
  simp only [CollatzResearch.WordTrace]
  refine ⟨79332268528002406244574415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105776358037336541659432553 79332268528002406244574415)
  ·
    refine ⟨118998402792003609366861623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79332268528002406244574415 118998402792003609366861623)
    ·
      refine ⟨178497604188005414050292435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118998402792003609366861623 178497604188005414050292435)
      ·
        refine ⟨267746406282008121075438653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178497604188005414050292435 267746406282008121075438653)
        ·
          refine ⟨100404902355753045403289495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267746406282008121075438653 100404902355753045403289495)
          ·
            refine ⟨150607353533629568104934243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100404902355753045403289495 150607353533629568104934243)
            ·
              refine ⟨225911030300444352157401365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150607353533629568104934243 225911030300444352157401365)
              ·
                refine ⟨10589579545333329007378189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225911030300444352157401365 10589579545333329007378189)
                ·
                  refine ⟨3971092329499998377766821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10589579545333329007378189 3971092329499998377766821)
                  ·
                    refine ⟨744579811781249695831279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971092329499998377766821 744579811781249695831279)
                    ·
                      rfl

theorem cell23_4350192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_4350192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350192 prefixEnd_4350192 := by exact prefixLift 4350192
  have htrace : WordTrace (prefixWord ++ tailWord_4350192) baseStart_4350192 baseEnd_4350192 := by
    simpa [prefixWord, tailWord_4350192, baseEnd_4350192] using wordTrace_append hprefix tailTrace_4350192
  have hstable : (prefixWord ++ tailWord_4350192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350192).length < 2 ^ (prefixWord ++ tailWord_4350192).sum := by decide
  have hdescent : baseEnd_4350192 < baseStart_4350192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350205 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 10]
def baseStart_4350205 : Nat := 118140960795 + 4350205 * 2 ^ 59
def prefixEnd_4350205 : Nat := 4983230072969 + 3 ^ 40 * 4350205 * 2
def baseEnd_4350205 : Nat := 248194012288028615181253

theorem tailTrace_4350205 : CollatzResearch.WordTrace tailWord_4350205 prefixEnd_4350205 248194012288028615181253 := by
  unfold tailWord_4350205
  simp only [CollatzResearch.WordTrace]
  refine ⟨158665011204957715709372069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105776674136638477139581379 158665011204957715709372069)
  ·
    refine ⟨29749689600929571695507263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158665011204957715709372069 29749689600929571695507263)
    ·
      refine ⟨44624534401394357543260895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29749689600929571695507263 44624534401394357543260895)
      ·
        refine ⟨66936801602091536314891343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44624534401394357543260895 66936801602091536314891343)
        ·
          refine ⟨100405202403137304472337015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66936801602091536314891343 100405202403137304472337015)
          ·
            refine ⟨150607803604705956708505523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100405202403137304472337015 150607803604705956708505523)
            ·
              refine ⟨225911705407058935062758285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150607803604705956708505523 225911705407058935062758285)
              ·
                refine ⟨84716889527647100648534357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225911705407058935062758285 84716889527647100648534357)
                ·
                  refine ⟨248194012288028615181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84716889527647100648534357 248194012288028615181253)
                  ·
                    rfl

theorem cell23_4350205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_4350205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350205 prefixEnd_4350205 := by exact prefixLift 4350205
  have htrace : WordTrace (prefixWord ++ tailWord_4350205) baseStart_4350205 baseEnd_4350205 := by
    simpa [prefixWord, tailWord_4350205, baseEnd_4350205] using wordTrace_append hprefix tailTrace_4350205
  have hstable : (prefixWord ++ tailWord_4350205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350205).length < 2 ^ (prefixWord ++ tailWord_4350205).sum := by decide
  have hdescent : baseEnd_4350205 < baseStart_4350205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350252 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_4350252 : Nat := 118140960795 + 4350252 * 2 ^ 59
def prefixEnd_4350252 : Nat := 4983230072969 + 3 ^ 40 * 4350252 * 2
def baseEnd_4350252 : Nat := 744590081394339617581187

theorem tailTrace_4350252 : CollatzResearch.WordTrace tailWord_4350252 prefixEnd_4350252 744590081394339617581187 := by
  unfold tailWord_4350252
  simp only [CollatzResearch.WordTrace]
  refine ⟨79333362717893721368166505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105777816957191628490888673 79333362717893721368166505)
  ·
    refine ⟨59500022038420291026124879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79333362717893721368166505 59500022038420291026124879)
    ·
      refine ⟨89250033057630436539187319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59500022038420291026124879 89250033057630436539187319)
      ·
        refine ⟨133875049586445654808780979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89250033057630436539187319 133875049586445654808780979)
        ·
          refine ⟨200812574379668482213171469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133875049586445654808780979 200812574379668482213171469)
          ·
            refine ⟨75304715392375680829939301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200812574379668482213171469 75304715392375680829939301)
            ·
              refine ⟨14119634136070440155613619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75304715392375680829939301 14119634136070440155613619)
              ·
                refine ⟨21179451204105660233420429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14119634136070440155613619 21179451204105660233420429)
                ·
                  refine ⟨7942294201539622587532661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21179451204105660233420429 7942294201539622587532661)
                  ·
                    refine ⟨744590081394339617581187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7942294201539622587532661 744590081394339617581187)
                    ·
                      rfl

theorem cell23_4350252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_4350252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350252 prefixEnd_4350252 := by exact prefixLift 4350252
  have htrace : WordTrace (prefixWord ++ tailWord_4350252) baseStart_4350252 baseEnd_4350252 := by
    simpa [prefixWord, tailWord_4350252, baseEnd_4350252] using wordTrace_append hprefix tailTrace_4350252
  have hstable : (prefixWord ++ tailWord_4350252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350252).length < 2 ^ (prefixWord ++ tailWord_4350252).sum := by decide
  have hdescent : baseEnd_4350252 < baseStart_4350252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350259 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 1, 5, 2]
def baseStart_4350259 : Nat := 118140960795 + 4350259 * 2 ^ 59
def prefixEnd_4350259 : Nat := 4983230072969 + 3 ^ 40 * 4350259 * 2
def baseEnd_4350259 : Nat := 2233773838547600325356029

theorem tailTrace_4350259 : CollatzResearch.WordTrace tailWord_4350259 prefixEnd_4350259 2233773838547600325356029 := by
  unfold tailWord_4350259
  simp only [CollatzResearch.WordTrace]
  refine ⟨158666980746762082931837831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105777987164508055287891887 158666980746762082931837831)
  ·
    refine ⟨238000471120143124397756747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158666980746762082931837831 238000471120143124397756747)
    ·
      refine ⟨357000706680214686596635121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238000471120143124397756747 357000706680214686596635121)
      ·
        refine ⟨267750530010161014947476341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357000706680214686596635121 267750530010161014947476341)
        ·
          refine ⟨25101612188452595151325907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 267750530010161014947476341 25101612188452595151325907)
          ·
            refine ⟨37652418282678892726988861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25101612188452595151325907 37652418282678892726988861)
            ·
              refine ⟨14119656856004584772620823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37652418282678892726988861 14119656856004584772620823)
              ·
                refine ⟨21179485284006877158931235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14119656856004584772620823 21179485284006877158931235)
                ·
                  refine ⟨31769227926010315738396853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21179485284006877158931235 31769227926010315738396853)
                  ·
                    refine ⟨2978365118063467100474705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31769227926010315738396853 2978365118063467100474705)
                    ·
                      refine ⟨2233773838547600325356029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978365118063467100474705 2233773838547600325356029)
                      ·
                        rfl

theorem cell23_4350259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5, 2].length) (baseStart_4350259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350259 prefixEnd_4350259 := by exact prefixLift 4350259
  have htrace : WordTrace (prefixWord ++ tailWord_4350259) baseStart_4350259 baseEnd_4350259 := by
    simpa [prefixWord, tailWord_4350259, baseEnd_4350259] using wordTrace_append hprefix tailTrace_4350259
  have hstable : (prefixWord ++ tailWord_4350259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350259).length < 2 ^ (prefixWord ++ tailWord_4350259).sum := by decide
  have hdescent : baseEnd_4350259 < baseStart_4350259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350272 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_4350272 : Nat := 118140960795 + 4350272 * 2 ^ 59
def prefixEnd_4350272 : Nat := 4983230072969 + 3 ^ 40 * 4350272 * 2
def baseEnd_4350272 : Nat := 2233780513796108774493469

theorem tailTrace_4350272 : CollatzResearch.WordTrace tailWord_4350272 prefixEnd_4350272 2233780513796108774493469 := by
  unfold tailWord_4350272
  simp only [CollatzResearch.WordTrace]
  refine ⟨79333727447857493076030535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105778303263809990768040713 79333727447857493076030535)
  ·
    refine ⟨119000591171786239614045803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79333727447857493076030535 119000591171786239614045803)
    ·
      refine ⟨178500886757679359421068705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119000591171786239614045803 178500886757679359421068705)
      ·
        refine ⟨133875665068259519565801529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178500886757679359421068705 133875665068259519565801529)
        ·
          refine ⟨100406748801194639674351147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133875665068259519565801529 100406748801194639674351147)
          ·
            refine ⟨150610123201791959511526721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100406748801194639674351147 150610123201791959511526721)
            ·
              refine ⟨112957592401343969633645041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150610123201791959511526721 112957592401343969633645041)
              ·
                refine ⟨84718194301007977225233781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112957592401343969633645041 84718194301007977225233781)
                ·
                  refine ⟨7942330715719497864865667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84718194301007977225233781 7942330715719497864865667)
                  ·
                    refine ⟨11913496073579246797298501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7942330715719497864865667 11913496073579246797298501)
                    ·
                      refine ⟨2233780513796108774493469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11913496073579246797298501 2233780513796108774493469)
                      ·
                        rfl

theorem cell23_4350272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_4350272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350272 prefixEnd_4350272 := by exact prefixLift 4350272
  have htrace : WordTrace (prefixWord ++ tailWord_4350272) baseStart_4350272 baseEnd_4350272 := by
    simpa [prefixWord, tailWord_4350272, baseEnd_4350272] using wordTrace_append hprefix tailTrace_4350272
  have hstable : (prefixWord ++ tailWord_4350272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350272).length < 2 ^ (prefixWord ++ tailWord_4350272).sum := by decide
  have hdescent : baseEnd_4350272 < baseStart_4350272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350273 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 6]
def baseStart_4350273 : Nat := 118140960795 + 4350273 * 2 ^ 59
def prefixEnd_4350273 : Nat := 4983230072969 + 3 ^ 40 * 4350273 * 2
def baseEnd_4350273 : Nat := 248197891919640363397885

theorem tailTrace_4350273 : CollatzResearch.WordTrace tailWord_4350273 prefixEnd_4350273 248197891919640363397885 := by
  unfold tailWord_4350273
  simp only [CollatzResearch.WordTrace]
  refine ⟨158667491368711363322847473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105778327579140908881898315 158667491368711363322847473)
  ·
    refine ⟨119000618526533522492135605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158667491368711363322847473 119000618526533522492135605)
    ·
      refine ⟨11156307986862517733637713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119000618526533522492135605 11156307986862517733637713)
      ·
        refine ⟨8367230990146888300228285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11156307986862517733637713 8367230990146888300228285)
        ·
          refine ⟨3137711621305083112585607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8367230990146888300228285 3137711621305083112585607)
          ·
            refine ⟨4706567431957624668878411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137711621305083112585607 4706567431957624668878411)
            ·
              refine ⟨7059851147936437003317617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706567431957624668878411 7059851147936437003317617)
              ·
                refine ⟨5294888360952327752488213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7059851147936437003317617 5294888360952327752488213)
                ·
                  refine ⟨248197891919640363397885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5294888360952327752488213 248197891919640363397885)
                  ·
                    rfl

theorem cell23_4350273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 6].length) (baseStart_4350273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350273 prefixEnd_4350273 := by exact prefixLift 4350273
  have htrace : WordTrace (prefixWord ++ tailWord_4350273) baseStart_4350273 baseEnd_4350273 := by
    simpa [prefixWord, tailWord_4350273, baseEnd_4350273] using wordTrace_append hprefix tailTrace_4350273
  have hstable : (prefixWord ++ tailWord_4350273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350273).length < 2 ^ (prefixWord ++ tailWord_4350273).sum := by decide
  have hdescent : baseEnd_4350273 < baseStart_4350273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350306 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4350306 : Nat := 118140960795 + 4350306 * 2 ^ 59
def prefixEnd_4350306 : Nat := 4983230072969 + 3 ^ 40 * 4350306 * 2
def baseEnd_4350306 : Nat := 2233797972138361641468313

theorem tailTrace_4350306 : CollatzResearch.WordTrace tailWord_4350306 prefixEnd_4350306 2233797972138361641468313 := by
  unfold tailWord_4350306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39667173744397952489699693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105779129985061206639199181 39667173744397952489699693)
  ·
    refine ⟨14875190154149232183637385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39667173744397952489699693 14875190154149232183637385)
    ·
      refine ⟨11156392615611924137728039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14875190154149232183637385 11156392615611924137728039)
      ·
        refine ⟨16734588923417886206592059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11156392615611924137728039 16734588923417886206592059)
        ·
          refine ⟨25101883385126829309888089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16734588923417886206592059 25101883385126829309888089)
          ·
            refine ⟨18826412538845121982416067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25101883385126829309888089 18826412538845121982416067)
            ·
              refine ⟨28239618808267682973624101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18826412538845121982416067 28239618808267682973624101)
              ·
                refine ⟨5294928526550190557554519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28239618808267682973624101 5294928526550190557554519)
                ·
                  refine ⟨7942392789825285836331779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5294928526550190557554519 7942392789825285836331779)
                  ·
                    refine ⟨11913589184737928754497669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7942392789825285836331779 11913589184737928754497669)
                    ·
                      refine ⟨2233797972138361641468313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11913589184737928754497669 2233797972138361641468313)
                      ·
                        rfl

theorem cell23_4350306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4350306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350306 prefixEnd_4350306 := by exact prefixLift 4350306
  have htrace : WordTrace (prefixWord ++ tailWord_4350306) baseStart_4350306 baseEnd_4350306 := by
    simpa [prefixWord, tailWord_4350306, baseEnd_4350306] using wordTrace_append hprefix tailTrace_4350306
  have hstable : (prefixWord ++ tailWord_4350306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350306).length < 2 ^ (prefixWord ++ tailWord_4350306).sum := by decide
  have hdescent : baseEnd_4350306 < baseStart_4350306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350346 : List Nat := [3, 1, 2, 5, 1, 1, 2, 8]
def baseStart_4350346 : Nat := 118140960795 + 4350346 * 2 ^ 59
def prefixEnd_4350346 : Nat := 4983230072969 + 3 ^ 40 * 4350346 * 2
def baseEnd_4350346 : Nat := 82734018939427462406227

theorem tailTrace_4350346 : CollatzResearch.WordTrace tailWord_4350346 prefixEnd_4350346 82734018939427462406227 := by
  unfold tailWord_4350346
  simp only [CollatzResearch.WordTrace]
  refine ⟨39667538474361724197563723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105780102598297931193503261 39667538474361724197563723)
  ·
    refine ⟨59501307711542586296345585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39667538474361724197563723 59501307711542586296345585)
    ·
      refine ⟨44625980783656939722259189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59501307711542586296345585 44625980783656939722259189)
      ·
        refine ⟨4183685698467838098961799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44625980783656939722259189 4183685698467838098961799)
        ·
          refine ⟨6275528547701757148442699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183685698467838098961799 6275528547701757148442699)
          ·
            refine ⟨9413292821552635722664049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275528547701757148442699 9413292821552635722664049)
            ·
              refine ⟨7059969616164476791998037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9413292821552635722664049 7059969616164476791998037)
              ·
                refine ⟨82734018939427462406227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7059969616164476791998037 82734018939427462406227)
                ·
                  rfl

theorem cell23_4350346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_4350346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350346 prefixEnd_4350346 := by exact prefixLift 4350346
  have htrace : WordTrace (prefixWord ++ tailWord_4350346) baseStart_4350346 baseEnd_4350346 := by
    simpa [prefixWord, tailWord_4350346, baseEnd_4350346] using wordTrace_append hprefix tailTrace_4350346
  have hstable : (prefixWord ++ tailWord_4350346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350346).length < 2 ^ (prefixWord ++ tailWord_4350346).sum := by decide
  have hdescent : baseEnd_4350346 < baseStart_4350346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350350 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_4350350 : Nat := 118140960795 + 4350350 * 2 ^ 59
def prefixEnd_4350350 : Nat := 4983230072969 + 3 ^ 40 * 4350350 * 2
def baseEnd_4350350 : Nat := 744606855095719823106037

theorem tailTrace_4350350 : CollatzResearch.WordTrace tailWord_4350350 prefixEnd_4350350 744606855095719823106037 := by
  unfold tailWord_4350350
  simp only [CollatzResearch.WordTrace]
  refine ⟨19833787473679050684175063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105780199859621603648933669 19833787473679050684175063)
  ·
    refine ⟨29750681210518576026262595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19833787473679050684175063 29750681210518576026262595)
    ·
      refine ⟨44626021815777864039393893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29750681210518576026262595 44626021815777864039393893)
      ·
        refine ⟨8367379090458349507386355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44626021815777864039393893 8367379090458349507386355)
        ·
          refine ⟨12551068635687524261079533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367379090458349507386355 12551068635687524261079533)
          ·
            refine ⟨4706650738382821597904825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12551068635687524261079533 4706650738382821597904825)
            ·
              refine ⟨3529988053787116198428619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4706650738382821597904825 3529988053787116198428619)
              ·
                refine ⟨5294982080680674297642929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529988053787116198428619 5294982080680674297642929)
                ·
                  refine ⟨3971236560510505723232197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294982080680674297642929 3971236560510505723232197)
                  ·
                    refine ⟨744606855095719823106037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971236560510505723232197 744606855095719823106037)
                    ·
                      rfl

theorem cell23_4350350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_4350350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350350 prefixEnd_4350350 := by exact prefixLift 4350350
  have htrace : WordTrace (prefixWord ++ tailWord_4350350) baseStart_4350350 baseEnd_4350350 := by
    simpa [prefixWord, tailWord_4350350, baseEnd_4350350] using wordTrace_append hprefix tailTrace_4350350
  have hstable : (prefixWord ++ tailWord_4350350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350350).length < 2 ^ (prefixWord ++ tailWord_4350350).sum := by decide
  have hdescent : baseEnd_4350350 < baseStart_4350350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350392 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_4350392 : Nat := 118140960795 + 4350392 * 2 ^ 59
def prefixEnd_4350392 : Nat := 4983230072969 + 3 ^ 40 * 4350392 * 2
def baseEnd_4350392 : Nat := 2233842131474648304992917

theorem tailTrace_4350392 : CollatzResearch.WordTrace tailWord_4350392 prefixEnd_4350392 2233842131474648304992917 := by
  unfold tailWord_4350392
  simp only [CollatzResearch.WordTrace]
  refine ⟨79335915827640123323214715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105781221103520164430952953 79335915827640123323214715)
  ·
    refine ⟨119003873741460184984822073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79335915827640123323214715 119003873741460184984822073)
    ·
      refine ⟨89252905306095138738616555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119003873741460184984822073 89252905306095138738616555)
      ·
        refine ⟨133879357959142708107924833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89252905306095138738616555 133879357959142708107924833)
        ·
          refine ⟨100409518469357031080943625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133879357959142708107924833 100409518469357031080943625)
          ·
            refine ⟨75307138852017773310707719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100409518469357031080943625 75307138852017773310707719)
            ·
              refine ⟨112960708278026659966061579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75307138852017773310707719 112960708278026659966061579)
              ·
                refine ⟨169441062417039989949092369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112960708278026659966061579 169441062417039989949092369)
                ·
                  refine ⟨127080796812779992461819277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169441062417039989949092369 127080796812779992461819277)
                  ·
                    refine ⟨47655298804792497173182229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127080796812779992461819277 47655298804792497173182229)
                    ·
                      refine ⟨2233842131474648304992917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47655298804792497173182229 2233842131474648304992917)
                      ·
                        rfl

theorem cell23_4350392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_4350392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350392 prefixEnd_4350392 := by exact prefixLift 4350392
  have htrace : WordTrace (prefixWord ++ tailWord_4350392) baseStart_4350392 baseEnd_4350392 := by
    simpa [prefixWord, tailWord_4350392, baseEnd_4350392] using wordTrace_append hprefix tailTrace_4350392
  have hstable : (prefixWord ++ tailWord_4350392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350392).length < 2 ^ (prefixWord ++ tailWord_4350392).sum := by decide
  have hdescent : baseEnd_4350392 < baseStart_4350392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350446 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_4350446 : Nat := 118140960795 + 4350446 * 2 ^ 59
def prefixEnd_4350446 : Nat := 4983230072969 + 3 ^ 40 * 4350446 * 2
def baseEnd_4350446 : Nat := 2233869859429991093717669

theorem tailTrace_4350446 : CollatzResearch.WordTrace tailWord_4350446 prefixEnd_4350446 2233869859429991093717669 := by
  unfold tailWord_4350446
  simp only [CollatzResearch.WordTrace]
  refine ⟨19834225149635576733611899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105782534131389742579263461 19834225149635576733611899)
  ·
    refine ⟨29751337724453365100417849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19834225149635576733611899 29751337724453365100417849)
    ·
      refine ⟨22313503293340023825313387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29751337724453365100417849 22313503293340023825313387)
      ·
        refine ⟨33470254940010035737970081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22313503293340023825313387 33470254940010035737970081)
        ·
          refine ⟨25102691205007526803477561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33470254940010035737970081 25102691205007526803477561)
          ·
            refine ⟨18827018403755645102608171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25102691205007526803477561 18827018403755645102608171)
            ·
              refine ⟨28240527605633467653912257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18827018403755645102608171 28240527605633467653912257)
              ·
                refine ⟨21180395704225100740434193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28240527605633467653912257 21180395704225100740434193)
                ·
                  refine ⟨15885296778168825555325645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21180395704225100740434193 15885296778168825555325645)
                  ·
                    refine ⟨5956986291813309583247117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15885296778168825555325645 5956986291813309583247117)
                    ·
                      refine ⟨2233869859429991093717669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5956986291813309583247117 2233869859429991093717669)
                      ·
                        rfl

theorem cell23_4350446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_4350446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350446 prefixEnd_4350446 := by exact prefixLift 4350446
  have htrace : WordTrace (prefixWord ++ tailWord_4350446) baseStart_4350446 baseEnd_4350446 := by
    simpa [prefixWord, tailWord_4350446, baseEnd_4350446] using wordTrace_append hprefix tailTrace_4350446
  have hstable : (prefixWord ++ tailWord_4350446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350446).length < 2 ^ (prefixWord ++ tailWord_4350446).sum := by decide
  have hdescent : baseEnd_4350446 < baseStart_4350446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350449 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_4350449 : Nat := 118140960795 + 4350449 * 2 ^ 59
def prefixEnd_4350449 : Nat := 4983230072969 + 3 ^ 40 * 4350449 * 2
def baseEnd_4350449 : Nat := 744623799957318193993385

theorem tailTrace_4350449 : CollatzResearch.WordTrace tailWord_4350449 prefixEnd_4350449 744623799957318193993385 := by
  unfold tailWord_4350449
  simp only [CollatzResearch.WordTrace]
  refine ⟨158673910616073745381254401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105782607077382496920836267 158673910616073745381254401)
  ·
    refine ⟨119005432962055309035940801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158673910616073745381254401 119005432962055309035940801)
    ·
      refine ⟨89254074721541481776955601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119005432962055309035940801 89254074721541481776955601)
      ·
        refine ⟨66940556041156111332716701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89254074721541481776955601 66940556041156111332716701)
        ·
          refine ⟨25102708515433541749768763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66940556041156111332716701 25102708515433541749768763)
          ·
            refine ⟨37654062773150312624653145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25102708515433541749768763 37654062773150312624653145)
            ·
              refine ⟨28240547079862734468489859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37654062773150312624653145 28240547079862734468489859)
              ·
                refine ⟨42360820619794101702734789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28240547079862734468489859 42360820619794101702734789)
                ·
                  refine ⟨7942653866211394069262773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42360820619794101702734789 7942653866211394069262773)
                  ·
                    refine ⟨744623799957318193993385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7942653866211394069262773 744623799957318193993385)
                    ·
                      rfl

theorem cell23_4350449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_4350449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350449 prefixEnd_4350449 := by exact prefixLift 4350449
  have htrace : WordTrace (prefixWord ++ tailWord_4350449) baseStart_4350449 baseEnd_4350449 := by
    simpa [prefixWord, tailWord_4350449, baseEnd_4350449] using wordTrace_append hprefix tailTrace_4350449
  have hstable : (prefixWord ++ tailWord_4350449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350449).length < 2 ^ (prefixWord ++ tailWord_4350449).sum := by decide
  have hdescent : baseEnd_4350449 < baseStart_4350449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350453 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 7]
def baseStart_4350453 : Nat := 118140960795 + 4350453 * 2 ^ 59
def prefixEnd_4350453 : Nat := 4983230072969 + 3 ^ 40 * 4350453 * 2
def baseEnd_4350453 : Nat := 248208161532730285147793

theorem tailTrace_4350453 : CollatzResearch.WordTrace tailWord_4350453 prefixEnd_4350453 248208161532730285147793 := by
  unfold tailWord_4350453
  simp only [CollatzResearch.WordTrace]
  refine ⟨158674056508059254064400013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105782704338706169376266675 158674056508059254064400013)
  ·
    refine ⟨59502771190522220274150005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158674056508059254064400013 59502771190522220274150005)
    ·
      refine ⟨5578384799111458150701563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59502771190522220274150005 5578384799111458150701563)
      ·
        refine ⟨8367577198667187226052345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5578384799111458150701563 8367577198667187226052345)
        ·
          refine ⟨6275682899000390419539259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8367577198667187226052345 6275682899000390419539259)
          ·
            refine ⟨9413524348500585629308889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275682899000390419539259 9413524348500585629308889)
            ·
              refine ⟨7060143261375439221981667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9413524348500585629308889 7060143261375439221981667)
              ·
                refine ⟨10590214892063158832972501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7060143261375439221981667 10590214892063158832972501)
                ·
                  refine ⟨248208161532730285147793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10590214892063158832972501 248208161532730285147793)
                  ·
                    rfl

theorem cell23_4350453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_4350453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350453 prefixEnd_4350453 := by exact prefixLift 4350453
  have htrace : WordTrace (prefixWord ++ tailWord_4350453) baseStart_4350453 baseEnd_4350453 := by
    simpa [prefixWord, tailWord_4350453, baseEnd_4350453] using wordTrace_append hprefix tailTrace_4350453
  have hstable : (prefixWord ++ tailWord_4350453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350453).length < 2 ^ (prefixWord ++ tailWord_4350453).sum := by decide
  have hdescent : baseEnd_4350453 < baseStart_4350453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350469 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_4350469 : Nat := 118140960795 + 4350469 * 2 ^ 59
def prefixEnd_4350469 : Nat := 4983230072969 + 3 ^ 40 * 4350469 * 2
def baseEnd_4350469 : Nat := 2233881669485044503730063

theorem tailTrace_4350469 : CollatzResearch.WordTrace tailWord_4350469 prefixEnd_4350469 2233881669485044503730063 := by
  unfold tailWord_4350469
  simp only [CollatzResearch.WordTrace]
  refine ⟨158674640076001288796982461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105783093384000859197988307 158674640076001288796982461)
  ·
    refine ⟨59502990028500483298868423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158674640076001288796982461 59502990028500483298868423)
    ·
      refine ⟨89254485042750724948302635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59502990028500483298868423 89254485042750724948302635)
      ·
        refine ⟨133881727564126087422453953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89254485042750724948302635 133881727564126087422453953)
        ·
          refine ⟨100411295673094565566840465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133881727564126087422453953 100411295673094565566840465)
          ·
            refine ⟨75308471754820924175130349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100411295673094565566840465 75308471754820924175130349)
            ·
              refine ⟨28240676908057846565673881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75308471754820924175130349 28240676908057846565673881)
              ·
                refine ⟨21180507681043384924255411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28240676908057846565673881 21180507681043384924255411)
                ·
                  refine ⟨31770761521565077386383117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21180507681043384924255411 31770761521565077386383117)
                  ·
                    refine ⟨11914035570586904019893669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31770761521565077386383117 11914035570586904019893669)
                    ·
                      refine ⟨2233881669485044503730063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11914035570586904019893669 2233881669485044503730063)
                      ·
                        rfl

theorem cell23_4350469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_4350469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350469 prefixEnd_4350469 := by exact prefixLift 4350469
  have htrace : WordTrace (prefixWord ++ tailWord_4350469) baseStart_4350469 baseEnd_4350469 := by
    simpa [prefixWord, tailWord_4350469, baseEnd_4350469] using wordTrace_append hprefix tailTrace_4350469
  have hstable : (prefixWord ++ tailWord_4350469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350469).length < 2 ^ (prefixWord ++ tailWord_4350469).sum := by decide
  have hdescent : baseEnd_4350469 < baseStart_4350469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350470 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4350470 : Nat := 118140960795 + 4350470 * 2 ^ 59
def prefixEnd_4350470 : Nat := 4983230072969 + 3 ^ 40 * 4350470 * 2
def baseEnd_4350470 : Nat := 248209131440633222201951

theorem tailTrace_4350470 : CollatzResearch.WordTrace tailWord_4350470 prefixEnd_4350470 248209131440633222201951 := by
  unfold tailWord_4350470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958583642156177061492777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105783117699331777311845909 4958583642156177061492777)
  ·
    refine ⟨3718937731617132796119583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4958583642156177061492777 3718937731617132796119583)
    ·
      refine ⟨5578406597425699194179375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718937731617132796119583 5578406597425699194179375)
      ·
        refine ⟨8367609896138548791269063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5578406597425699194179375 8367609896138548791269063)
        ·
          refine ⟨12551414844207823186903595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367609896138548791269063 12551414844207823186903595)
          ·
            refine ⟨18827122266311734780355393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12551414844207823186903595 18827122266311734780355393)
            ·
              refine ⟨14120341699733801085266545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18827122266311734780355393 14120341699733801085266545)
              ·
                refine ⟨10590256274800350813949909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14120341699733801085266545 10590256274800350813949909)
                ·
                  refine ⟨248209131440633222201951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10590256274800350813949909 248209131440633222201951)
                  ·
                    rfl

theorem cell23_4350470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4350470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350470 prefixEnd_4350470 := by exact prefixLift 4350470
  have htrace : WordTrace (prefixWord ++ tailWord_4350470) baseStart_4350470 baseEnd_4350470 := by
    simpa [prefixWord, tailWord_4350470, baseEnd_4350470] using wordTrace_append hprefix tailTrace_4350470
  have hstable : (prefixWord ++ tailWord_4350470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350470).length < 2 ^ (prefixWord ++ tailWord_4350470).sum := by decide
  have hdescent : baseEnd_4350470 < baseStart_4350470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350487 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 5]
def baseStart_4350487 : Nat := 118140960795 + 4350487 * 2 ^ 59
def prefixEnd_4350487 : Nat := 4983230072969 + 3 ^ 40 * 4350487 * 2
def baseEnd_4350487 : Nat := 248210101348536159256109

theorem tailTrace_4350487 : CollatzResearch.WordTrace tailWord_4350487 prefixEnd_4350487 248210101348536159256109 := by
  unfold tailWord_4350487
  simp only [CollatzResearch.WordTrace]
  refine ⟨158675296589936077871137715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105783531059957385247425143 158675296589936077871137715)
  ·
    refine ⟨238012944884904116806706573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158675296589936077871137715 238012944884904116806706573)
    ·
      refine ⟨89254854331839043802514965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238012944884904116806706573 89254854331839043802514965)
      ·
        refine ⟨4183821296804955178242889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89254854331839043802514965 4183821296804955178242889)
        ·
          refine ⟨3137865972603716383682167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4183821296804955178242889 3137865972603716383682167)
          ·
            refine ⟨4706798958905574575523251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137865972603716383682167 4706798958905574575523251)
            ·
              refine ⟨7060198438358361863284877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706798958905574575523251 7060198438358361863284877)
              ·
                refine ⟨2647574414384385698731829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7060198438358361863284877 2647574414384385698731829)
                ·
                  refine ⟨248210101348536159256109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2647574414384385698731829 248210101348536159256109)
                  ·
                    rfl

theorem cell23_4350487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 5].length) (baseStart_4350487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350487 prefixEnd_4350487 := by exact prefixLift 4350487
  have htrace : WordTrace (prefixWord ++ tailWord_4350487) baseStart_4350487 baseEnd_4350487 := by
    simpa [prefixWord, tailWord_4350487, baseEnd_4350487] using wordTrace_append hprefix tailTrace_4350487
  have hstable : (prefixWord ++ tailWord_4350487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350487).length < 2 ^ (prefixWord ++ tailWord_4350487).sum := by decide
  have hdescent : baseEnd_4350487 < baseStart_4350487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350513 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 1, 4]
def baseStart_4350513 : Nat := 118140960795 + 4350513 * 2 ^ 59
def prefixEnd_4350513 : Nat := 4983230072969 + 3 ^ 40 * 4350513 * 2
def baseEnd_4350513 : Nat := 744634754211280777193287

theorem tailTrace_4350513 : CollatzResearch.WordTrace tailWord_4350513 prefixEnd_4350513 744634754211280777193287 := by
  unfold tailWord_4350513
  simp only [CollatzResearch.WordTrace]
  refine ⟨158676244887841884311584193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105784163258561256207722795 158676244887841884311584193)
  ·
    refine ⟨119007183665881413233688145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158676244887841884311584193 119007183665881413233688145)
    ·
      refine ⟨89255387749411059925266109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119007183665881413233688145 89255387749411059925266109)
      ·
        refine ⟨33470770406029147471974791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89255387749411059925266109 33470770406029147471974791)
        ·
          refine ⟨50206155609043721207962187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33470770406029147471974791 50206155609043721207962187)
          ·
            refine ⟨75309233413565581811943281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50206155609043721207962187 75309233413565581811943281)
            ·
              refine ⟨56481925060174186358957461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75309233413565581811943281 56481925060174186358957461)
              ·
                refine ⟨2647590237195664985576131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56481925060174186358957461 2647590237195664985576131)
                ·
                  refine ⟨3971385355793497478364197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647590237195664985576131 3971385355793497478364197)
                  ·
                    refine ⟨744634754211280777193287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971385355793497478364197 744634754211280777193287)
                    ·
                      rfl

theorem cell23_4350513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_4350513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350513 prefixEnd_4350513 := by exact prefixLift 4350513
  have htrace : WordTrace (prefixWord ++ tailWord_4350513) baseStart_4350513 baseEnd_4350513 := by
    simpa [prefixWord, tailWord_4350513, baseEnd_4350513] using wordTrace_append hprefix tailTrace_4350513
  have hstable : (prefixWord ++ tailWord_4350513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350513).length < 2 ^ (prefixWord ++ tailWord_4350513).sum := by decide
  have hdescent : baseEnd_4350513 < baseStart_4350513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350563 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 2, 3, 2]
def baseStart_4350563 : Nat := 118140960795 + 4350563 * 2 ^ 59
def prefixEnd_4350563 : Nat := 4983230072969 + 3 ^ 40 * 4350563 * 2
def baseEnd_4350563 : Nat := 2233929936666567135954631

theorem tailTrace_4350563 : CollatzResearch.WordTrace tailWord_4350563 prefixEnd_4350563 2233929936666567135954631 := by
  unfold tailWord_4350563
  simp only [CollatzResearch.WordTrace]
  refine ⟨158678068537660742850904343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105785379025107161900602895 158678068537660742850904343)
  ·
    refine ⟨238017102806491114276356515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158678068537660742850904343 238017102806491114276356515)
    ·
      refine ⟨357025654209736671414534773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238017102806491114276356515 357025654209736671414534773)
      ·
        refine ⟨33471155082162812945112635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 357025654209736671414534773 33471155082162812945112635)
        ·
          refine ⟨50206732623244219417668953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33471155082162812945112635 50206732623244219417668953)
          ·
            refine ⟨37655049467433164563251715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50206732623244219417668953 37655049467433164563251715)
            ·
              refine ⟨56482574201149746844877573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37655049467433164563251715 56482574201149746844877573)
              ·
                refine ⟨10590482662715577533414545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56482574201149746844877573 10590482662715577533414545)
                ·
                  refine ⟨7942861997036683150060909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10590482662715577533414545 7942861997036683150060909)
                  ·
                    refine ⟨2978573248888756181272841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7942861997036683150060909 2978573248888756181272841)
                    ·
                      refine ⟨2233929936666567135954631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978573248888756181272841 2233929936666567135954631)
                      ·
                        rfl

theorem cell23_4350563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_4350563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350563 prefixEnd_4350563 := by exact prefixLift 4350563
  have htrace : WordTrace (prefixWord ++ tailWord_4350563) baseStart_4350563 baseEnd_4350563 := by
    simpa [prefixWord, tailWord_4350563, baseEnd_4350563] using wordTrace_append hprefix tailTrace_4350563
  have hstable : (prefixWord ++ tailWord_4350563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350563).length < 2 ^ (prefixWord ++ tailWord_4350563).sum := by decide
  have hdescent : baseEnd_4350563 < baseStart_4350563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350569 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_4350569 : Nat := 118140960795 + 4350569 * 2 ^ 59
def prefixEnd_4350569 : Nat := 4983230072969 + 3 ^ 40 * 4350569 * 2
def baseEnd_4350569 : Nat := 744644339183498037493201

theorem tailTrace_4350569 : CollatzResearch.WordTrace tailWord_4350569 prefixEnd_4350569 744644339183498037493201 := by
  unfold tailWord_4350569
  simp only [CollatzResearch.WordTrace]
  refine ⟨158678287375639005875622761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105785524917092670583748507 158678287375639005875622761)
  ·
    refine ⟨119008715531729254406717071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158678287375639005875622761 119008715531729254406717071)
    ·
      refine ⟨178513073297593881610075607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119008715531729254406717071 178513073297593881610075607)
      ·
        refine ⟨267769609946390822415113411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178513073297593881610075607 267769609946390822415113411)
        ·
          refine ⟨401654414919586233622670117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267769609946390822415113411 401654414919586233622670117)
          ·
            refine ⟨75310202797422418804250647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 401654414919586233622670117 75310202797422418804250647)
            ·
              refine ⟨112965304196133628206375971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75310202797422418804250647 112965304196133628206375971)
              ·
                refine ⟨169447956294200442309563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112965304196133628206375971 169447956294200442309563957)
                ·
                  refine ⟨15885745902581291466521621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169447956294200442309563957 15885745902581291466521621)
                  ·
                    refine ⟨744644339183498037493201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15885745902581291466521621 744644339183498037493201)
                    ·
                      rfl

theorem cell23_4350569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_4350569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350569 prefixEnd_4350569 := by exact prefixLift 4350569
  have htrace : WordTrace (prefixWord ++ tailWord_4350569) baseStart_4350569 baseEnd_4350569 := by
    simpa [prefixWord, tailWord_4350569, baseEnd_4350569] using wordTrace_append hprefix tailTrace_4350569
  have hstable : (prefixWord ++ tailWord_4350569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350569).length < 2 ^ (prefixWord ++ tailWord_4350569).sum := by decide
  have hdescent : baseEnd_4350569 < baseStart_4350569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350593 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_4350593 : Nat := 118140960795 + 4350593 * 2 ^ 59
def prefixEnd_4350593 : Nat := 4983230072969 + 3 ^ 40 * 4350593 * 2
def baseEnd_4350593 : Nat := 2233945341086202018579493

theorem tailTrace_4350593 : CollatzResearch.WordTrace tailWord_4350593 prefixEnd_4350593 2233945341086202018579493 := by
  unfold tailWord_4350593
  simp only [CollatzResearch.WordTrace]
  refine ⟨158679162727552057974496433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105786108485034705316330955 158679162727552057974496433)
  ·
    refine ⟨119009372045664043480872325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158679162727552057974496433 119009372045664043480872325)
    ·
      refine ⟨22314257258562008152663561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119009372045664043480872325 22314257258562008152663561)
      ·
        refine ⟨16735692943921506114497671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22314257258562008152663561 16735692943921506114497671)
        ·
          refine ⟨25103539415882259171746507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16735692943921506114497671 25103539415882259171746507)
          ·
            refine ⟨37655309123823388757619761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25103539415882259171746507 37655309123823388757619761)
            ·
              refine ⟨28241481842867541568214821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37655309123823388757619761 28241481842867541568214821)
              ·
                refine ⟨5295277845537664044040279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28241481842867541568214821 5295277845537664044040279)
                ·
                  refine ⟨7942916768306496066060419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5295277845537664044040279 7942916768306496066060419)
                  ·
                    refine ⟨11914375152459744099090629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7942916768306496066060419 11914375152459744099090629)
                    ·
                      refine ⟨2233945341086202018579493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11914375152459744099090629 2233945341086202018579493)
                      ·
                        rfl

theorem cell23_4350593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_4350593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350593 prefixEnd_4350593 := by exact prefixLift 4350593
  have htrace : WordTrace (prefixWord ++ tailWord_4350593) baseStart_4350593 baseEnd_4350593 := by
    simpa [prefixWord, tailWord_4350593, baseEnd_4350593] using wordTrace_append hprefix tailTrace_4350593
  have hstable : (prefixWord ++ tailWord_4350593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350593).length < 2 ^ (prefixWord ++ tailWord_4350593).sum := by decide
  have hdescent : baseEnd_4350593 < baseStart_4350593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350609 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_4350609 : Nat := 118140960795 + 4350609 * 2 ^ 59
def prefixEnd_4350609 : Nat := 4983230072969 + 3 ^ 40 * 4350609 * 2
def baseEnd_4350609 : Nat := 2233953556776673955979419

theorem tailTrace_4350609 : CollatzResearch.WordTrace tailWord_4350609 prefixEnd_4350609 2233953556776673955979419 := by
  unfold tailWord_4350609
  simp only [CollatzResearch.WordTrace]
  refine ⟨158679746295494092707078881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105786497530329395138052587 158679746295494092707078881)
  ·
    refine ⟨119009809721620569530309161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158679746295494092707078881 119009809721620569530309161)
    ·
      refine ⟨89257357291215427147731871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119009809721620569530309161 89257357291215427147731871)
      ·
        refine ⟨133886035936823140721597807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89257357291215427147731871 133886035936823140721597807)
        ·
          refine ⟨200829053905234711082396711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133886035936823140721597807 200829053905234711082396711)
          ·
            refine ⟨301243580857852066623595067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200829053905234711082396711 301243580857852066623595067)
            ·
              refine ⟨451865371286778099935392601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301243580857852066623595067 451865371286778099935392601)
              ·
                refine ⟨338899028465083574951544451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451865371286778099935392601 338899028465083574951544451)
                ·
                  refine ⟨508348542697625362427316677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338899028465083574951544451 508348542697625362427316677)
                  ·
                    refine ⟨95315351755804755455121877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 508348542697625362427316677 95315351755804755455121877)
                    ·
                      refine ⟨2233953556776673955979419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95315351755804755455121877 2233953556776673955979419)
                      ·
                        rfl

theorem cell23_4350609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_4350609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350609 prefixEnd_4350609 := by exact prefixLift 4350609
  have htrace : WordTrace (prefixWord ++ tailWord_4350609) baseStart_4350609 baseEnd_4350609 := by
    simpa [prefixWord, tailWord_4350609, baseEnd_4350609] using wordTrace_append hprefix tailTrace_4350609
  have hstable : (prefixWord ++ tailWord_4350609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350609).length < 2 ^ (prefixWord ++ tailWord_4350609).sum := by decide
  have hdescent : baseEnd_4350609 < baseStart_4350609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350610 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_4350610 : Nat := 118140960795 + 4350610 * 2 ^ 59
def prefixEnd_4350610 : Nat := 4983230072969 + 3 ^ 40 * 4350610 * 2
def baseEnd_4350610 : Nat := 2233954070257328452066915

theorem tailTrace_4350610 : CollatzResearch.WordTrace tailWord_4350610 prefixEnd_4350610 2233954070257328452066915 := by
  unfold tailWord_4350610
  simp only [CollatzResearch.WordTrace]
  refine ⟨39669945692122617469466321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105786521845660313251910189 39669945692122617469466321)
  ·
    refine ⟨29752459269091963102099741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39669945692122617469466321 29752459269091963102099741)
    ·
      refine ⟨11157172225909486163287403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29752459269091963102099741 11157172225909486163287403)
      ·
        refine ⟨16735758338864229244931105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11157172225909486163287403 16735758338864229244931105)
        ·
          refine ⟨12551818754148171933698329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16735758338864229244931105 12551818754148171933698329)
          ·
            refine ⟨9413864065611128950273747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12551818754148171933698329 9413864065611128950273747)
            ·
              refine ⟨14120796098416693425410621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9413864065611128950273747 14120796098416693425410621)
              ·
                refine ⟨5295298536906260034528983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14120796098416693425410621 5295298536906260034528983)
                ·
                  refine ⟨7942947805359390051793475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5295298536906260034528983 7942947805359390051793475)
                  ·
                    refine ⟨11914421708039085077690213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7942947805359390051793475 11914421708039085077690213)
                    ·
                      refine ⟨2233954070257328452066915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11914421708039085077690213 2233954070257328452066915)
                      ·
                        rfl

theorem cell23_4350610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_4350610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350610 prefixEnd_4350610 := by exact prefixLift 4350610
  have htrace : WordTrace (prefixWord ++ tailWord_4350610) baseStart_4350610 baseEnd_4350610 := by
    simpa [prefixWord, tailWord_4350610, baseEnd_4350610] using wordTrace_append hprefix tailTrace_4350610
  have hstable : (prefixWord ++ tailWord_4350610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350610).length < 2 ^ (prefixWord ++ tailWord_4350610).sum := by decide
  have hdescent : baseEnd_4350610 < baseStart_4350610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350619 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_4350619 : Nat := 118140960795 + 4350619 * 2 ^ 59
def prefixEnd_4350619 : Nat := 4983230072969 + 3 ^ 40 * 4350619 * 2
def baseEnd_4350619 : Nat := 2233958691583218916854373

theorem tailTrace_4350619 : CollatzResearch.WordTrace tailWord_4350619 prefixEnd_4350619 2233958691583218916854373 := by
  unfold tailWord_4350619
  simp only [CollatzResearch.WordTrace]
  refine ⟨158680111025457864414942911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105786740683638576276628607 158680111025457864414942911)
  ·
    refine ⟨238020166538186796622414367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158680111025457864414942911 238020166538186796622414367)
    ·
      refine ⟨357030249807280194933621551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238020166538186796622414367 357030249807280194933621551)
      ·
        refine ⟨535545374710920292400432327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357030249807280194933621551 535545374710920292400432327)
        ·
          refine ⟨803318062066380438600648491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535545374710920292400432327 803318062066380438600648491)
          ·
            refine ⟨1204977093099570657900972737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803318062066380438600648491 1204977093099570657900972737)
            ·
              refine ⟨903732819824677993425729553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204977093099570657900972737 903732819824677993425729553)
              ·
                refine ⟨677799614868508495069297165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903732819824677993425729553 677799614868508495069297165)
                ·
                  refine ⟨254174855575690685650986437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677799614868508495069297165 254174855575690685650986437)
                  ·
                    refine ⟨47657785420442003559559957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254174855575690685650986437 47657785420442003559559957)
                    ·
                      refine ⟨2233958691583218916854373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47657785420442003559559957 2233958691583218916854373)
                      ·
                        rfl

theorem cell23_4350619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_4350619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350619 prefixEnd_4350619 := by exact prefixLift 4350619
  have htrace : WordTrace (prefixWord ++ tailWord_4350619) baseStart_4350619 baseEnd_4350619 := by
    simpa [prefixWord, tailWord_4350619, baseEnd_4350619] using wordTrace_append hprefix tailTrace_4350619
  have hstable : (prefixWord ++ tailWord_4350619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350619).length < 2 ^ (prefixWord ++ tailWord_4350619).sum := by decide
  have hdescent : baseEnd_4350619 < baseStart_4350619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350620 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_4350620 : Nat := 118140960795 + 4350620 * 2 ^ 59
def prefixEnd_4350620 : Nat := 4983230072969 + 3 ^ 40 * 4350620 * 2
def baseEnd_4350620 : Nat := 744653068354624470980623

theorem tailTrace_4350620 : CollatzResearch.WordTrace tailWord_4350620 prefixEnd_4350620 744653068354624470980623 := by
  unfold tailWord_4350620
  simp only [CollatzResearch.WordTrace]
  refine ⟨79340073749227120792864657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105786764998969494390486209 79340073749227120792864657)
  ·
    refine ⟨59505055311920340594648493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79340073749227120792864657 59505055311920340594648493)
    ·
      refine ⟨22314395741970127722993185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59505055311920340594648493 22314395741970127722993185)
      ·
        refine ⟨16735796806477595792244889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22314395741970127722993185 16735796806477595792244889)
        ·
          refine ⟨12551847604858196844183667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16735796806477595792244889 12551847604858196844183667)
          ·
            refine ⟨18827771407287295266275501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12551847604858196844183667 18827771407287295266275501)
            ·
              refine ⟨7060414277732735724853313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18827771407287295266275501 7060414277732735724853313)
              ·
                refine ⟨5295310708299551793639985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7060414277732735724853313 5295310708299551793639985)
                ·
                  refine ⟨3971483031224663845229989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5295310708299551793639985 3971483031224663845229989)
                  ·
                    refine ⟨744653068354624470980623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971483031224663845229989 744653068354624470980623)
                    ·
                      rfl

theorem cell23_4350620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_4350620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350620 prefixEnd_4350620 := by exact prefixLift 4350620
  have htrace : WordTrace (prefixWord ++ tailWord_4350620) baseStart_4350620 baseEnd_4350620 := by
    simpa [prefixWord, tailWord_4350620, baseEnd_4350620] using wordTrace_append hprefix tailTrace_4350620
  have hstable : (prefixWord ++ tailWord_4350620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350620).length < 2 ^ (prefixWord ++ tailWord_4350620).sum := by decide
  have hdescent : baseEnd_4350620 < baseStart_4350620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350637 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4350637 : Nat := 118140960795 + 4350637 * 2 ^ 59
def prefixEnd_4350637 : Nat := 4983230072969 + 3 ^ 40 * 4350637 * 2
def baseEnd_4350637 : Nat := 744655978078333282143097

theorem tailTrace_4350637 : CollatzResearch.WordTrace tailWord_4350637 prefixEnd_4350637 744655978078333282143097 := by
  unfold tailWord_4350637
  simp only [CollatzResearch.WordTrace]
  refine ⟨158680767539392653489098165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105787178359595102326065443 158680767539392653489098165)
  ·
    refine ⟨14876321956818061264602953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158680767539392653489098165 14876321956818061264602953)
    ·
      refine ⟨11157241467613545948452215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14876321956818061264602953 11157241467613545948452215)
      ·
        refine ⟨16735862201420318922678323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11157241467613545948452215 16735862201420318922678323)
        ·
          refine ⟨25103793302130478384017485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16735862201420318922678323 25103793302130478384017485)
          ·
            refine ⟨9413922488298929394006557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25103793302130478384017485 9413922488298929394006557)
            ·
              refine ⟨3530220933112098522752459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9413922488298929394006557 3530220933112098522752459)
              ·
                refine ⟨5295331399668147784128689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530220933112098522752459 5295331399668147784128689)
                ·
                  refine ⟨3971498549751110838096517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5295331399668147784128689 3971498549751110838096517)
                  ·
                    refine ⟨744655978078333282143097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971498549751110838096517 744655978078333282143097)
                    ·
                      rfl

theorem cell23_4350637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4350637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350637 prefixEnd_4350637 := by exact prefixLift 4350637
  have htrace : WordTrace (prefixWord ++ tailWord_4350637) baseStart_4350637 baseEnd_4350637 := by
    simpa [prefixWord, tailWord_4350637, baseEnd_4350637] using wordTrace_append hprefix tailTrace_4350637
  have hstable : (prefixWord ++ tailWord_4350637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350637).length < 2 ^ (prefixWord ++ tailWord_4350637).sum := by decide
  have hdescent : baseEnd_4350637 < baseStart_4350637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350643 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 3]
def baseStart_4350643 : Nat := 118140960795 + 4350643 * 2 ^ 59
def prefixEnd_4350643 : Nat := 4983230072969 + 3 ^ 40 * 4350643 * 2
def baseEnd_4350643 : Nat := 2233971015118926822954263

theorem tailTrace_4350643 : CollatzResearch.WordTrace tailWord_4350643 prefixEnd_4350643 2233971015118926822954263 := by
  unfold tailWord_4350643
  simp only [CollatzResearch.WordTrace]
  refine ⟨158680986377370916513816583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105787324251580611009211055 158680986377370916513816583)
  ·
    refine ⟨238021479566056374770724875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158680986377370916513816583 238021479566056374770724875)
    ·
      refine ⟨357032219349084562156087313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238021479566056374770724875 357032219349084562156087313)
      ·
        refine ⟨267774164511813421617065485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357032219349084562156087313 267774164511813421617065485)
        ·
          refine ⟨100415311691930033106399557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267774164511813421617065485 100415311691930033106399557)
          ·
            refine ⟨18827870942236881207449917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100415311691930033106399557 18827870942236881207449917)
            ·
              refine ⟨7060451603338830452793719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18827870942236881207449917 7060451603338830452793719)
              ·
                refine ⟨10590677405008245679190579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7060451603338830452793719 10590677405008245679190579)
                ·
                  refine ⟨15886016107512368518785869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10590677405008245679190579 15886016107512368518785869)
                  ·
                    refine ⟨5957256040317138194544701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15886016107512368518785869 5957256040317138194544701)
                    ·
                      refine ⟨2233971015118926822954263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5957256040317138194544701 2233971015118926822954263)
                      ·
                        rfl

theorem cell23_4350643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_4350643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350643 prefixEnd_4350643 := by exact prefixLift 4350643
  have htrace : WordTrace (prefixWord ++ tailWord_4350643) baseStart_4350643 baseEnd_4350643 := by
    simpa [prefixWord, tailWord_4350643, baseEnd_4350643] using wordTrace_append hprefix tailTrace_4350643
  have hstable : (prefixWord ++ tailWord_4350643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350643).length < 2 ^ (prefixWord ++ tailWord_4350643).sum := by decide
  have hdescent : baseEnd_4350643 < baseStart_4350643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350656 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_4350656 : Nat := 118140960795 + 4350656 * 2 ^ 59
def prefixEnd_4350656 : Nat := 4983230072969 + 3 ^ 40 * 4350656 * 2
def baseEnd_4350656 : Nat := 2233977690367435272091703

theorem tailTrace_4350656 : CollatzResearch.WordTrace tailWord_4350656 prefixEnd_4350656 2233977690367435272091703 := by
  unfold tailWord_4350656
  simp only [CollatzResearch.WordTrace]
  refine ⟨79340730263161909867019911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105787640350882546489359881 79340730263161909867019911)
  ·
    refine ⟨119011095394742864800529867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79340730263161909867019911 119011095394742864800529867)
    ·
      refine ⟨178516643092114297200794801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119011095394742864800529867 178516643092114297200794801)
      ·
        refine ⟨133887482319085722900596101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178516643092114297200794801 133887482319085722900596101)
        ·
          refine ⟨25103902934828573043861769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133887482319085722900596101 25103902934828573043861769)
          ·
            refine ⟨18827927201121429782896327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25103902934828573043861769 18827927201121429782896327)
            ·
              refine ⟨28241890801682144674344491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18827927201121429782896327 28241890801682144674344491)
              ·
                refine ⟨42362836202523217011516737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28241890801682144674344491 42362836202523217011516737)
                ·
                  refine ⟨31772127151892412758637553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42362836202523217011516737 31772127151892412758637553)
                  ·
                    refine ⟨23829095363919309568978165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31772127151892412758637553 23829095363919309568978165)
                    ·
                      refine ⟨2233977690367435272091703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23829095363919309568978165 2233977690367435272091703)
                      ·
                        rfl

theorem cell23_4350656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_4350656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350656 prefixEnd_4350656 := by exact prefixLift 4350656
  have htrace : WordTrace (prefixWord ++ tailWord_4350656) baseStart_4350656 baseEnd_4350656 := by
    simpa [prefixWord, tailWord_4350656, baseEnd_4350656] using wordTrace_append hprefix tailTrace_4350656
  have hstable : (prefixWord ++ tailWord_4350656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350656).length < 2 ^ (prefixWord ++ tailWord_4350656).sum := by decide
  have hdescent : baseEnd_4350656 < baseStart_4350656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350660 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_4350660 : Nat := 118140960795 + 4350660 * 2 ^ 59
def prefixEnd_4350660 : Nat := 4983230072969 + 3 ^ 40 * 4350660 * 2
def baseEnd_4350660 : Nat := 2233979744290053256441685

theorem tailTrace_4350660 : CollatzResearch.WordTrace tailWord_4350660 prefixEnd_4350660 2233979744290053256441685 := by
  unfold tailWord_4350660
  simp only [CollatzResearch.WordTrace]
  refine ⟨79340803209154664208592717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105787737612206218944790289 79340803209154664208592717)
  ·
    refine ⟨29752801203432999078222269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79340803209154664208592717 29752801203432999078222269)
    ·
      refine ⟨11157300451287374654333351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29752801203432999078222269 11157300451287374654333351)
      ·
        refine ⟨16735950676931061981500027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11157300451287374654333351 16735950676931061981500027)
        ·
          refine ⟨25103926015396592972250041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16735950676931061981500027 25103926015396592972250041)
          ·
            refine ⟨18827944511547444729187531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25103926015396592972250041 18827944511547444729187531)
            ·
              refine ⟨28241916767321167093781297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18827944511547444729187531 28241916767321167093781297)
              ·
                refine ⟨21181437575490875320335973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28241916767321167093781297 21181437575490875320335973)
                ·
                  refine ⟨3971519545404539122562995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21181437575490875320335973 3971519545404539122562995)
                  ·
                    refine ⟨5957279318106808683844493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3971519545404539122562995 5957279318106808683844493)
                    ·
                      refine ⟨2233979744290053256441685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5957279318106808683844493 2233979744290053256441685)
                      ·
                        rfl

theorem cell23_4350660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_4350660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350660 prefixEnd_4350660 := by exact prefixLift 4350660
  have htrace : WordTrace (prefixWord ++ tailWord_4350660) baseStart_4350660 baseEnd_4350660 := by
    simpa [prefixWord, tailWord_4350660, baseEnd_4350660] using wordTrace_append hprefix tailTrace_4350660
  have hstable : (prefixWord ++ tailWord_4350660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350660).length < 2 ^ (prefixWord ++ tailWord_4350660).sum := by decide
  have hdescent : baseEnd_4350660 < baseStart_4350660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350723 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 5]
def baseStart_4350723 : Nat := 118140960795 + 4350723 * 2 ^ 59
def prefixEnd_4350723 : Nat := 4983230072969 + 3 ^ 40 * 4350723 * 2
def baseEnd_4350723 : Nat := 248223565952365167772655

theorem tailTrace_4350723 : CollatzResearch.WordTrace tailWord_4350723 prefixEnd_4350723 248223565952365167772655 := by
  unfold tailWord_4350723
  simp only [CollatzResearch.WordTrace]
  refine ⟨158683904217081090176728823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105789269478054060117819215 158683904217081090176728823)
  ·
    refine ⟨238025856325621635265093235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158683904217081090176728823 238025856325621635265093235)
    ·
      refine ⟨357038784488432452897639853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238025856325621635265093235 357038784488432452897639853)
      ·
        refine ⟨133889544183162169836614945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357038784488432452897639853 133889544183162169836614945)
        ·
          refine ⟨100417158137371627377461209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133889544183162169836614945 100417158137371627377461209)
          ·
            refine ⟨75312868603028720533095907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100417158137371627377461209 75312868603028720533095907)
            ·
              refine ⟨112969302904543080799643861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75312868603028720533095907 112969302904543080799643861)
              ·
                refine ⟨2647718036825228456241653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112969302904543080799643861 2647718036825228456241653)
                ·
                  refine ⟨248223565952365167772655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2647718036825228456241653 248223565952365167772655)
                  ·
                    rfl

theorem cell23_4350723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 5].length) (baseStart_4350723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350723 prefixEnd_4350723 := by exact prefixLift 4350723
  have htrace : WordTrace (prefixWord ++ tailWord_4350723) baseStart_4350723 baseEnd_4350723 := by
    simpa [prefixWord, tailWord_4350723, baseEnd_4350723] using wordTrace_append hprefix tailTrace_4350723
  have hstable : (prefixWord ++ tailWord_4350723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350723).length < 2 ^ (prefixWord ++ tailWord_4350723).sum := by decide
  have hdescent : baseEnd_4350723 < baseStart_4350723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350760 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_4350760 : Nat := 118140960795 + 4350760 * 2 ^ 59
def prefixEnd_4350760 : Nat := 4983230072969 + 3 ^ 40 * 4350760 * 2
def baseEnd_4350760 : Nat := 2234031092355502865191225

theorem tailTrace_4350760 : CollatzResearch.WordTrace tailWord_4350760 prefixEnd_4350760 2234031092355502865191225 := by
  unfold tailWord_4350760
  simp only [CollatzResearch.WordTrace]
  refine ⟨79342626858973522747912867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105790169145298030330550489 79342626858973522747912867)
  ·
    refine ⟨119013940288460284121869301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79342626858973522747912867 119013940288460284121869301)
    ·
      refine ⟨11157556902043151636425247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119013940288460284121869301 11157556902043151636425247)
      ·
        refine ⟨16736335353064727454637871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11157556902043151636425247 16736335353064727454637871)
        ·
          refine ⟨25104503029597091181956807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16736335353064727454637871 25104503029597091181956807)
          ·
            refine ⟨37656754544395636772935211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25104503029597091181956807 37656754544395636772935211)
            ·
              refine ⟨56485131816593455159402817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37656754544395636772935211 56485131816593455159402817)
              ·
                refine ⟨42363848862445091369552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56485131816593455159402817 42363848862445091369552113)
                ·
                  refine ⟨31772886646833818527164085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42363848862445091369552113 31772886646833818527164085)
                  ·
                    refine ⟨2978708123140670486921633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31772886646833818527164085 2978708123140670486921633)
                    ·
                      refine ⟨2234031092355502865191225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978708123140670486921633 2234031092355502865191225)
                      ·
                        rfl

theorem cell23_4350760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_4350760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350760 prefixEnd_4350760 := by exact prefixLift 4350760
  have htrace : WordTrace (prefixWord ++ tailWord_4350760) baseStart_4350760 baseEnd_4350760 := by
    simpa [prefixWord, tailWord_4350760, baseEnd_4350760] using wordTrace_append hprefix tailTrace_4350760
  have hstable : (prefixWord ++ tailWord_4350760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350760).length < 2 ^ (prefixWord ++ tailWord_4350760).sum := by decide
  have hdescent : baseEnd_4350760 < baseStart_4350760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350774 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_4350774 : Nat := 118140960795 + 4350774 * 2 ^ 59
def prefixEnd_4350774 : Nat := 4983230072969 + 3 ^ 40 * 4350774 * 2
def baseEnd_4350774 : Nat := 248226475676073978935129

theorem tailTrace_4350774 : CollatzResearch.WordTrace tailWord_4350774 prefixEnd_4350774 248226475676073978935129 := by
  unfold tailWord_4350774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917860271243520367927211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105790509559930883924556917 9917860271243520367927211)
  ·
    refine ⟨14876790406865280551890817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9917860271243520367927211 14876790406865280551890817)
    ·
      refine ⟨11157592805148960413918113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14876790406865280551890817 11157592805148960413918113)
      ·
        refine ⟨8368194603861720310438585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11157592805148960413918113 8368194603861720310438585)
        ·
          refine ⟨6276145952896290232828939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8368194603861720310438585 6276145952896290232828939)
          ·
            refine ⟨9414218929344435349243409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6276145952896290232828939 9414218929344435349243409)
            ·
              refine ⟨7060664197008326511932557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9414218929344435349243409 7060664197008326511932557)
              ·
                refine ⟨2647749073878122441974709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7060664197008326511932557 2647749073878122441974709)
                ·
                  refine ⟨248226475676073978935129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2647749073878122441974709 248226475676073978935129)
                  ·
                    rfl

theorem cell23_4350774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_4350774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350774 prefixEnd_4350774 := by exact prefixLift 4350774
  have htrace : WordTrace (prefixWord ++ tailWord_4350774) baseStart_4350774 baseEnd_4350774 := by
    simpa [prefixWord, tailWord_4350774, baseEnd_4350774] using wordTrace_append hprefix tailTrace_4350774
  have hstable : (prefixWord ++ tailWord_4350774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350774).length < 2 ^ (prefixWord ++ tailWord_4350774).sum := by decide
  have hdescent : baseEnd_4350774 < baseStart_4350774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350857 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 3]
def baseStart_4350857 : Nat := 118140960795 + 4350857 * 2 ^ 59
def prefixEnd_4350857 : Nat := 4983230072969 + 3 ^ 40 * 4350857 * 2
def baseEnd_4350857 : Nat := 2234080899978988985678279

theorem tailTrace_4350857 : CollatzResearch.WordTrace tailWord_4350857 prefixEnd_4350857 2234080899978988985678279 := by
  unfold tailWord_4350857
  simp only [CollatzResearch.WordTrace]
  refine ⟨158688791598595631062106825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105792527732397087374737883 158688791598595631062106825)
  ·
    refine ⟨119016593698946723296580119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158688791598595631062106825 119016593698946723296580119)
    ·
      refine ⟨178524890548420084944870179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119016593698946723296580119 178524890548420084944870179)
      ·
        refine ⟨267787335822630127417305269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178524890548420084944870179 267787335822630127417305269)
        ·
          refine ⟨25105062733371574445372369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 267787335822630127417305269 25105062733371574445372369)
          ·
            refine ⟨18828797050028680834029277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25105062733371574445372369 18828797050028680834029277)
            ·
              refine ⟨7060798893760755312760979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18828797050028680834029277 7060798893760755312760979)
              ·
                refine ⟨10591198340641132969141469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7060798893760755312760979 10591198340641132969141469)
                ·
                  refine ⟨3971699377740424863428051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10591198340641132969141469 3971699377740424863428051)
                  ·
                    refine ⟨5957549066610637295142077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3971699377740424863428051 5957549066610637295142077)
                    ·
                      refine ⟨2234080899978988985678279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5957549066610637295142077 2234080899978988985678279)
                      ·
                        rfl

theorem cell23_4350857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_4350857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350857 prefixEnd_4350857 := by exact prefixLift 4350857
  have htrace : WordTrace (prefixWord ++ tailWord_4350857) baseStart_4350857 baseEnd_4350857 := by
    simpa [prefixWord, tailWord_4350857, baseEnd_4350857] using wordTrace_append hprefix tailTrace_4350857
  have hstable : (prefixWord ++ tailWord_4350857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350857).length < 2 ^ (prefixWord ++ tailWord_4350857).sum := by decide
  have hdescent : baseEnd_4350857 < baseStart_4350857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350873 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_4350873 : Nat := 118140960795 + 4350873 * 2 ^ 59
def prefixEnd_4350873 : Nat := 4983230072969 + 3 ^ 40 * 4350873 * 2
def baseEnd_4350873 : Nat := 744696371889820307692735

theorem tailTrace_4350873 : CollatzResearch.WordTrace tailWord_4350873 prefixEnd_4350873 744696371889820307692735 := by
  unfold tailWord_4350873
  simp only [CollatzResearch.WordTrace]
  refine ⟨158689375166537665794689273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105792916777691777196459515 158689375166537665794689273)
  ·
    refine ⟨119017031374903249346016955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158689375166537665794689273 119017031374903249346016955)
    ·
      refine ⟨178525547062354874019025433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119017031374903249346016955 178525547062354874019025433)
      ·
        refine ⟨133894160296766155514269075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178525547062354874019025433 133894160296766155514269075)
        ·
          refine ⟨200841240445149233271403613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133894160296766155514269075 200841240445149233271403613)
          ·
            refine ⟨75315465166930962476776355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200841240445149233271403613 75315465166930962476776355)
            ·
              refine ⟨112973197750396443715164533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75315465166930962476776355 112973197750396443715164533)
              ·
                refine ⟨10591237289099666598296675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112973197750396443715164533 10591237289099666598296675)
                ·
                  refine ⟨15886855933649499897445013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10591237289099666598296675 15886855933649499897445013)
                  ·
                    refine ⟨744696371889820307692735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15886855933649499897445013 744696371889820307692735)
                    ·
                      rfl

theorem cell23_4350873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_4350873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350873 prefixEnd_4350873 := by exact prefixLift 4350873
  have htrace : WordTrace (prefixWord ++ tailWord_4350873) baseStart_4350873 baseEnd_4350873 := by
    simpa [prefixWord, tailWord_4350873, baseEnd_4350873] using wordTrace_append hprefix tailTrace_4350873
  have hstable : (prefixWord ++ tailWord_4350873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350873).length < 2 ^ (prefixWord ++ tailWord_4350873).sum := by decide
  have hdescent : baseEnd_4350873 < baseStart_4350873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350880 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 6, 2]
def baseStart_4350880 : Nat := 118140960795 + 4350880 * 2 ^ 59
def prefixEnd_4350880 : Nat := 4983230072969 + 3 ^ 40 * 4350880 * 2
def baseEnd_4350880 : Nat := 2234092710034042395690673

theorem tailTrace_4350880 : CollatzResearch.WordTrace tailWord_4350880 prefixEnd_4350880 2234092710034042395690673 := by
  unfold tailWord_4350880
  simp only [CollatzResearch.WordTrace]
  refine ⟨79344815238756152995097047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105793086985008203993462729 79344815238756152995097047)
  ·
    refine ⟨119017222858134229492645571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79344815238756152995097047 119017222858134229492645571)
    ·
      refine ⟨178525834287201344238968357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119017222858134229492645571 178525834287201344238968357)
      ·
        refine ⟨33473593928850252044806567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178525834287201344238968357 33473593928850252044806567)
        ·
          refine ⟨50210390893275378067209851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33473593928850252044806567 50210390893275378067209851)
          ·
            refine ⟨75315586339913067100814777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50210390893275378067209851 75315586339913067100814777)
            ·
              refine ⟨56486689754934800325611083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75315586339913067100814777 56486689754934800325611083)
              ·
                refine ⟨84730034632402200488416625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56486689754934800325611083 84730034632402200488416625)
                ·
                  refine ⟨63547525974301650366312469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84730034632402200488416625 63547525974301650366312469)
                  ·
                    refine ⟨2978790280045389860920897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63547525974301650366312469 2978790280045389860920897)
                    ·
                      refine ⟨2234092710034042395690673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978790280045389860920897 2234092710034042395690673)
                      ·
                        rfl

theorem cell23_4350880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_4350880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350880 prefixEnd_4350880 := by exact prefixLift 4350880
  have htrace : WordTrace (prefixWord ++ tailWord_4350880) baseStart_4350880 baseEnd_4350880 := by
    simpa [prefixWord, tailWord_4350880, baseEnd_4350880] using wordTrace_append hprefix tailTrace_4350880
  have hstable : (prefixWord ++ tailWord_4350880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350880).length < 2 ^ (prefixWord ++ tailWord_4350880).sum := by decide
  have hdescent : baseEnd_4350880 < baseStart_4350880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350883 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5]
def baseStart_4350883 : Nat := 118140960795 + 4350883 * 2 ^ 59
def prefixEnd_4350883 : Nat := 4983230072969 + 3 ^ 40 * 4350883 * 2
def baseEnd_4350883 : Nat := 2234094250476005883953159

theorem tailTrace_4350883 : CollatzResearch.WordTrace tailWord_4350883 prefixEnd_4350883 2234094250476005883953159 := by
  unfold tailWord_4350883
  simp only [CollatzResearch.WordTrace]
  refine ⟨158689739896501437502553303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105793159931000958335035535 158689739896501437502553303)
  ·
    refine ⟨238034609844752156253829955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158689739896501437502553303 238034609844752156253829955)
    ·
      refine ⟨357051914767128234380744933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238034609844752156253829955 357051914767128234380744933)
      ·
        refine ⟨66947234018836543946389675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 357051914767128234380744933 66947234018836543946389675)
        ·
          refine ⟨100420851028254815919584513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66947234018836543946389675 100420851028254815919584513)
          ·
            refine ⟨75315638271191111939688385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100420851028254815919584513 75315638271191111939688385)
            ·
              refine ⟨56486728703393333954766289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75315638271191111939688385 56486728703393333954766289)
              ·
                refine ⟨42365046527545000466074717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56486728703393333954766289 42365046527545000466074717)
                ·
                  refine ⟨15886892447829375174778019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42365046527545000466074717 15886892447829375174778019)
                  ·
                    refine ⟨23830338671744062762167029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15886892447829375174778019 23830338671744062762167029)
                    ·
                      refine ⟨2234094250476005883953159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23830338671744062762167029 2234094250476005883953159)
                      ·
                        rfl

theorem cell23_4350883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_4350883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350883 prefixEnd_4350883 := by exact prefixLift 4350883
  have htrace : WordTrace (prefixWord ++ tailWord_4350883) baseStart_4350883 baseEnd_4350883 := by
    simpa [prefixWord, tailWord_4350883, baseEnd_4350883] using wordTrace_append hprefix tailTrace_4350883
  have hstable : (prefixWord ++ tailWord_4350883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350883).length < 2 ^ (prefixWord ++ tailWord_4350883).sum := by decide
  have hdescent : baseEnd_4350883 < baseStart_4350883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350902 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4350902 : Nat := 118140960795 + 4350902 * 2 ^ 59
def prefixEnd_4350902 : Nat := 4983230072969 + 3 ^ 40 * 4350902 * 2
def baseEnd_4350902 : Nat := 744701335536147103205191

theorem tailTrace_4350902 : CollatzResearch.WordTrace tailWord_4350902 prefixEnd_4350902 744701335536147103205191 := by
  unfold tailWord_4350902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918152055214537734218435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105793621922288402498329973 9918152055214537734218435)
  ·
    refine ⟨14877228082821806601327653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9918152055214537734218435 14877228082821806601327653)
    ·
      refine ⟨2789480265529088737748935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14877228082821806601327653 2789480265529088737748935)
      ·
        refine ⟨4184220398293633106623403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789480265529088737748935 4184220398293633106623403)
        ·
          refine ⟨6276330597440449659935105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4184220398293633106623403 6276330597440449659935105)
          ·
            refine ⟨4707247948080337244951329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6276330597440449659935105 4707247948080337244951329)
            ·
              refine ⟨3530435961060252933713497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4707247948080337244951329 3530435961060252933713497)
              ·
                refine ⟨2647826970795189700285123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3530435961060252933713497 2647826970795189700285123)
                ·
                  refine ⟨3971740456192784550427685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647826970795189700285123 3971740456192784550427685)
                  ·
                    refine ⟨744701335536147103205191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971740456192784550427685 744701335536147103205191)
                    ·
                      rfl

theorem cell23_4350902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4350902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350902 prefixEnd_4350902 := by exact prefixLift 4350902
  have htrace : WordTrace (prefixWord ++ tailWord_4350902) baseStart_4350902 baseEnd_4350902 := by
    simpa [prefixWord, tailWord_4350902, baseEnd_4350902] using wordTrace_append hprefix tailTrace_4350902
  have hstable : (prefixWord ++ tailWord_4350902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350902).length < 2 ^ (prefixWord ++ tailWord_4350902).sum := by decide
  have hdescent : baseEnd_4350902 < baseStart_4350902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350910 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4350910 : Nat := 118140960795 + 4350910 * 2 ^ 59
def prefixEnd_4350910 : Nat := 4983230072969 + 3 ^ 40 * 4350910 * 2
def baseEnd_4350910 : Nat := 2234108114453677278315535

theorem tailTrace_4350910 : CollatzResearch.WordTrace tailWord_4350910 prefixEnd_4350910 2234108114453677278315535 := by
  unfold tailWord_4350910
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836340583425452639223273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105793816444935747409190789 19836340583425452639223273)
  ·
    refine ⟨14877255437569089479417455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19836340583425452639223273 14877255437569089479417455)
    ·
      refine ⟨22315883156353634219126183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877255437569089479417455 22315883156353634219126183)
      ·
        refine ⟨33473824734530451328689275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22315883156353634219126183 33473824734530451328689275)
        ·
          refine ⟨50210737101795676993033913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33473824734530451328689275 50210737101795676993033913)
          ·
            refine ⟨37658052826346757744775435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50210737101795676993033913 37658052826346757744775435)
            ·
              refine ⟨56487079239520136617163153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37658052826346757744775435 56487079239520136617163153)
              ·
                refine ⟨42365309429640102462872365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56487079239520136617163153 42365309429640102462872365)
                ·
                  refine ⟨15886991036115038423577137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42365309429640102462872365 15886991036115038423577137)
                  ·
                    refine ⟨11915243277086278817682853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15886991036115038423577137 11915243277086278817682853)
                    ·
                      refine ⟨2234108114453677278315535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11915243277086278817682853 2234108114453677278315535)
                      ·
                        rfl

theorem cell23_4350910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4350910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350910 prefixEnd_4350910 := by exact prefixLift 4350910
  have htrace : WordTrace (prefixWord ++ tailWord_4350910) baseStart_4350910 baseEnd_4350910 := by
    simpa [prefixWord, tailWord_4350910, baseEnd_4350910] using wordTrace_append hprefix tailTrace_4350910
  have hstable : (prefixWord ++ tailWord_4350910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350910).length < 2 ^ (prefixWord ++ tailWord_4350910).sum := by decide
  have hdescent : baseEnd_4350910 < baseStart_4350910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350934 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4350934 : Nat := 118140960795 + 4350934 * 2 ^ 59
def prefixEnd_4350934 : Nat := 4983230072969 + 3 ^ 40 * 4350934 * 2
def baseEnd_4350934 : Nat := 2234120437989385184415425

theorem tailTrace_4350934 : CollatzResearch.WordTrace tailWord_4350934 prefixEnd_4350934 2234120437989385184415425 := by
  unfold tailWord_4350934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918225001207292075791241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105794400012877782141773237 9918225001207292075791241)
  ·
    refine ⟨7438668750905469056843431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9918225001207292075791241 7438668750905469056843431)
    ·
      refine ⟨11158003126358203585265147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7438668750905469056843431 11158003126358203585265147)
      ·
        refine ⟨16737004689537305377897721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11158003126358203585265147 16737004689537305377897721)
        ·
          refine ⟨12552753517152979033423291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16737004689537305377897721 12552753517152979033423291)
          ·
            refine ⟨18829130275729468550134937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12552753517152979033423291 18829130275729468550134937)
            ·
              refine ⟨14121847706797101412601203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18829130275729468550134937 14121847706797101412601203)
              ·
                refine ⟨21182771560195652118901805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14121847706797101412601203 21182771560195652118901805)
                ·
                  refine ⟨7943539335073369544588177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21182771560195652118901805 7943539335073369544588177)
                  ·
                    refine ⟨5957654501305027158441133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7943539335073369544588177 5957654501305027158441133)
                    ·
                      refine ⟨2234120437989385184415425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5957654501305027158441133 2234120437989385184415425)
                      ·
                        rfl

theorem cell23_4350934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4350934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350934 prefixEnd_4350934 := by exact prefixLift 4350934
  have htrace : WordTrace (prefixWord ++ tailWord_4350934) baseStart_4350934 baseEnd_4350934 := by
    simpa [prefixWord, tailWord_4350934, baseEnd_4350934] using wordTrace_append hprefix tailTrace_4350934
  have hstable : (prefixWord ++ tailWord_4350934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350934).length < 2 ^ (prefixWord ++ tailWord_4350934).sum := by decide
  have hdescent : baseEnd_4350934 < baseStart_4350934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350947 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 3]
def baseStart_4350947 : Nat := 118140960795 + 4350947 * 2 ^ 59
def prefixEnd_4350947 : Nat := 4983230072969 + 3 ^ 40 * 4350947 * 2
def baseEnd_4350947 : Nat := 2234127113237893633552865

theorem tailTrace_4350947 : CollatzResearch.WordTrace tailWord_4350947 prefixEnd_4350947 2234127113237893633552865 := by
  unfold tailWord_4350947
  simp only [CollatzResearch.WordTrace]
  refine ⟨158692074168269576432883095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105794716112179717621922063 158692074168269576432883095)
  ·
    refine ⟨238038111252404364649324643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158692074168269576432883095 238038111252404364649324643)
    ·
      refine ⟨357057166878606546973986965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238038111252404364649324643 357057166878606546973986965)
      ·
        refine ⟨16737054697434681889405639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 357057166878606546973986965 16737054697434681889405639)
        ·
          refine ⟨25105582046152022834108459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16737054697434681889405639 25105582046152022834108459)
          ·
            refine ⟨37658373069228034251162689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25105582046152022834108459 37658373069228034251162689)
            ·
              refine ⟨28243779801921025688372017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37658373069228034251162689 28243779801921025688372017)
              ·
                refine ⟨21182834851440769266279013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28243779801921025688372017 21182834851440769266279013)
                ·
                  refine ⟨3971781534645144237427315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21182834851440769266279013 3971781534645144237427315)
                  ·
                    refine ⟨5957672301967716356140973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3971781534645144237427315 5957672301967716356140973)
                    ·
                      refine ⟨2234127113237893633552865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5957672301967716356140973 2234127113237893633552865)
                      ·
                        rfl

theorem cell23_4350947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_4350947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350947 prefixEnd_4350947 := by exact prefixLift 4350947
  have htrace : WordTrace (prefixWord ++ tailWord_4350947) baseStart_4350947 baseEnd_4350947 := by
    simpa [prefixWord, tailWord_4350947, baseEnd_4350947] using wordTrace_append hprefix tailTrace_4350947
  have hstable : (prefixWord ++ tailWord_4350947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350947).length < 2 ^ (prefixWord ++ tailWord_4350947).sum := by decide
  have hdescent : baseEnd_4350947 < baseStart_4350947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350951 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4350951 : Nat := 118140960795 + 4350951 * 2 ^ 59
def prefixEnd_4350951 : Nat := 4983230072969 + 3 ^ 40 * 4350951 * 2
def baseEnd_4350951 : Nat := 2234129167160511617902847

theorem tailTrace_4350951 : CollatzResearch.WordTrace tailWord_4350951 prefixEnd_4350951 2234129167160511617902847 := by
  unfold tailWord_4350951
  simp only [CollatzResearch.WordTrace]
  refine ⟨158692220060255085116028707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105794813373503390077352471 158692220060255085116028707)
  ·
    refine ⟨238038330090382627674043061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158692220060255085116028707 238038330090382627674043061)
    ·
      refine ⟨22316093445973371344441537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238038330090382627674043061 22316093445973371344441537)
      ·
        refine ⟨16737070084480028508331153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22316093445973371344441537 16737070084480028508331153)
        ·
          refine ⟨12552802563360021381248365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16737070084480028508331153 12552802563360021381248365)
          ·
            refine ⟨4707300961260008017968137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12552802563360021381248365 4707300961260008017968137)
            ·
              refine ⟨3530475720945006013476103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4707300961260008017968137 3530475720945006013476103)
              ·
                refine ⟨5295713581417509020214155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530475720945006013476103 5295713581417509020214155)
                ·
                  refine ⟨7943570372126263530321233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5295713581417509020214155 7943570372126263530321233)
                  ·
                    refine ⟨5957677779094697647740925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7943570372126263530321233 5957677779094697647740925)
                    ·
                      refine ⟨2234129167160511617902847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5957677779094697647740925 2234129167160511617902847)
                      ·
                        rfl

theorem cell23_4350951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4350951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350951 prefixEnd_4350951 := by exact prefixLift 4350951
  have htrace : WordTrace (prefixWord ++ tailWord_4350951) baseStart_4350951 baseEnd_4350951 := by
    simpa [prefixWord, tailWord_4350951, baseEnd_4350951] using wordTrace_append hprefix tailTrace_4350951
  have hstable : (prefixWord ++ tailWord_4350951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350951).length < 2 ^ (prefixWord ++ tailWord_4350951).sum := by decide
  have hdescent : baseEnd_4350951 < baseStart_4350951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4350978 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4350978 : Nat := 118140960795 + 4350978 * 2 ^ 59
def prefixEnd_4350978 : Nat := 4983230072969 + 3 ^ 40 * 4350978 * 2
def baseEnd_4350978 : Nat := 2234143031138183012265223

theorem tailTrace_4350978 : CollatzResearch.WordTrace tailWord_4350978 prefixEnd_4350978 2234143031138183012265223 := by
  unfold tailWord_4350978
  simp only [CollatzResearch.WordTrace]
  refine ⟨39673301207789317181815397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105795469887438179151507725 39673301207789317181815397)
  ·
    refine ⟨7438743976460496971590387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39673301207789317181815397 7438743976460496971590387)
    ·
      refine ⟨11158115964690745457385581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7438743976460496971590387 11158115964690745457385581)
      ·
        refine ⟨4184293486759029546519593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11158115964690745457385581 4184293486759029546519593)
        ·
          refine ⟨3138220115069272159889695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4184293486759029546519593 3138220115069272159889695)
          ·
            refine ⟨4707330172603908239834543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138220115069272159889695 4707330172603908239834543)
            ·
              refine ⟨7060995258905862359751815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4707330172603908239834543 7060995258905862359751815)
              ·
                refine ⟨10591492888358793539627723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7060995258905862359751815 10591492888358793539627723)
                ·
                  refine ⟨15887239332538190309441585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10591492888358793539627723 15887239332538190309441585)
                  ·
                    refine ⟨11915429499403642732081189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15887239332538190309441585 11915429499403642732081189)
                    ·
                      refine ⟨2234143031138183012265223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11915429499403642732081189 2234143031138183012265223)
                      ·
                        rfl

theorem cell23_4350978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4350978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4350978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4350978 prefixEnd_4350978 := by exact prefixLift 4350978
  have htrace : WordTrace (prefixWord ++ tailWord_4350978) baseStart_4350978 baseEnd_4350978 := by
    simpa [prefixWord, tailWord_4350978, baseEnd_4350978] using wordTrace_append hprefix tailTrace_4350978
  have hstable : (prefixWord ++ tailWord_4350978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4350978).length < 2 ^ (prefixWord ++ tailWord_4350978).sum := by decide
  have hdescent : baseEnd_4350978 < baseStart_4350978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4350978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351038 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4351038 : Nat := 118140960795 + 4351038 * 2 ^ 59
def prefixEnd_4351038 : Nat := 4983230072969 + 3 ^ 40 * 4351038 * 2
def baseEnd_4351038 : Nat := 2234173839977452777514947

theorem tailTrace_4351038 : CollatzResearch.WordTrace tailWord_4351038 prefixEnd_4351038 2234173839977452777514947 := by
  unfold tailWord_4351038
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836924151367487371805721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105796928807293265982963845 19836924151367487371805721)
  ·
    refine ⟨14877693113525615528854291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19836924151367487371805721 14877693113525615528854291)
    ·
      refine ⟨22316539670288423293281437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877693113525615528854291 22316539670288423293281437)
      ·
        refine ⟨8368702376358158734980539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22316539670288423293281437 8368702376358158734980539)
        ·
          refine ⟨12553053564537238102470809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8368702376358158734980539 12553053564537238102470809)
          ·
            refine ⟨9414790173402928576853107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12553053564537238102470809 9414790173402928576853107)
            ·
              refine ⟨14122185260104392865279661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9414790173402928576853107 14122185260104392865279661)
              ·
                refine ⟨5295819472539147324479873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14122185260104392865279661 5295819472539147324479873)
                ·
                  refine ⟨3971864604404360493359905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5295819472539147324479873 3971864604404360493359905)
                  ·
                    refine ⟨2978898453303270370019929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3971864604404360493359905 2978898453303270370019929)
                    ·
                      refine ⟨2234173839977452777514947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978898453303270370019929 2234173839977452777514947)
                      ·
                        rfl

theorem cell23_4351038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4351038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351038 prefixEnd_4351038 := by exact prefixLift 4351038
  have htrace : WordTrace (prefixWord ++ tailWord_4351038) baseStart_4351038 baseEnd_4351038 := by
    simpa [prefixWord, tailWord_4351038, baseEnd_4351038] using wordTrace_append hprefix tailTrace_4351038
  have hstable : (prefixWord ++ tailWord_4351038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351038).length < 2 ^ (prefixWord ++ tailWord_4351038).sum := by decide
  have hdescent : baseEnd_4351038 < baseStart_4351038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351040 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_4351040 : Nat := 118140960795 + 4351040 * 2 ^ 59
def prefixEnd_4351040 : Nat := 4983230072969 + 3 ^ 40 * 4351040 * 2
def baseEnd_4351040 : Nat := 744724955646253923229979

theorem tailTrace_4351040 : CollatzResearch.WordTrace tailWord_4351040 prefixEnd_4351040 744724955646253923229979 := by
  unfold tailWord_4351040
  simp only [CollatzResearch.WordTrace]
  refine ⟨79347733078466326658009287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105796977437955102210679049 79347733078466326658009287)
  ·
    refine ⟨119021599617699489987013931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79347733078466326658009287 119021599617699489987013931)
    ·
      refine ⟨178532399426549234980520897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119021599617699489987013931 178532399426549234980520897)
      ·
        refine ⟨133899299569911926235390673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178532399426549234980520897 133899299569911926235390673)
        ·
          refine ⟨100424474677433944676543005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133899299569911926235390673 100424474677433944676543005)
          ·
            refine ⟨37659178004037729253703627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100424474677433944676543005 37659178004037729253703627)
            ·
              refine ⟨56488767006056593880555441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37659178004037729253703627 56488767006056593880555441)
              ·
                refine ⟨42366575254542445410416581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56488767006056593880555441 42366575254542445410416581)
                ·
                  refine ⟨7943732860226708514453109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42366575254542445410416581 7943732860226708514453109)
                  ·
                    refine ⟨744724955646253923229979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7943732860226708514453109 744724955646253923229979)
                    ·
                      rfl

theorem cell23_4351040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_4351040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351040 prefixEnd_4351040 := by exact prefixLift 4351040
  have htrace : WordTrace (prefixWord ++ tailWord_4351040) baseStart_4351040 baseEnd_4351040 := by
    simpa [prefixWord, tailWord_4351040, baseEnd_4351040] using wordTrace_append hprefix tailTrace_4351040
  have hstable : (prefixWord ++ tailWord_4351040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351040).length < 2 ^ (prefixWord ++ tailWord_4351040).sum := by decide
  have hdescent : baseEnd_4351040 < baseStart_4351040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351074 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_4351074 : Nat := 118140960795 + 4351074 * 2 ^ 59
def prefixEnd_4351074 : Nat := 4983230072969 + 3 ^ 40 * 4351074 * 2
def baseEnd_4351074 : Nat := 744730775093671545554927

theorem tailTrace_4351074 : CollatzResearch.WordTrace tailWord_4351074 prefixEnd_4351074 744730775093671545554927 := by
  unfold tailWord_4351074
  simp only [CollatzResearch.WordTrace]
  refine ⟨39674176559702369280689069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105797804159206318081837517 39674176559702369280689069)
  ·
    refine ⟨14877816209888388480258401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39674176559702369280689069 14877816209888388480258401)
    ·
      refine ⟨11158362157416291360193801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14877816209888388480258401 11158362157416291360193801)
      ·
        refine ⟨8368771618062218520145351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11158362157416291360193801 8368771618062218520145351)
        ·
          refine ⟨12553157427093327780218027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8368771618062218520145351 12553157427093327780218027)
          ·
            refine ⟨18829736140639991670327041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12553157427093327780218027 18829736140639991670327041)
            ·
              refine ⟨14122302105479993752745281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18829736140639991670327041 14122302105479993752745281)
              ·
                refine ⟨10591726579109995314558961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14122302105479993752745281 10591726579109995314558961)
                ·
                  refine ⟨7943794934332496485919221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10591726579109995314558961 7943794934332496485919221)
                  ·
                    refine ⟨744730775093671545554927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7943794934332496485919221 744730775093671545554927)
                    ·
                      rfl

theorem cell23_4351074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_4351074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351074 prefixEnd_4351074 := by exact prefixLift 4351074
  have htrace : WordTrace (prefixWord ++ tailWord_4351074) baseStart_4351074 baseEnd_4351074 := by
    simpa [prefixWord, tailWord_4351074, baseEnd_4351074] using wordTrace_append hprefix tailTrace_4351074
  have hstable : (prefixWord ++ tailWord_4351074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351074).length < 2 ^ (prefixWord ++ tailWord_4351074).sum := by decide
  have hdescent : baseEnd_4351074 < baseStart_4351074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351077 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4351077 : Nat := 118140960795 + 4351077 * 2 ^ 59
def prefixEnd_4351077 : Nat := 4983230072969 + 3 ^ 40 * 4351077 * 2
def baseEnd_4351077 : Nat := 2234193865722978124927267

theorem tailTrace_4351077 : CollatzResearch.WordTrace tailWord_4351077 prefixEnd_4351077 2234193865722978124927267 := by
  unfold tailWord_4351077
  simp only [CollatzResearch.WordTrace]
  refine ⟨158696815657798608635115485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105797877105199072423410323 158696815657798608635115485)
  ·
    refine ⟨59511305871674478238168307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158696815657798608635115485 59511305871674478238168307)
    ·
      refine ⟨89266958807511717357252461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59511305871674478238168307 89266958807511717357252461)
      ·
        refine ⟨33475109552816894008969673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89266958807511717357252461 33475109552816894008969673)
        ·
          refine ⟨25106332164612670506727255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33475109552816894008969673 25106332164612670506727255)
          ·
            refine ⟨37659498246919005760090883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25106332164612670506727255 37659498246919005760090883)
            ·
              refine ⟨56489247370378508640136325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37659498246919005760090883 56489247370378508640136325)
              ·
                refine ⟨10591733881945970370025561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56489247370378508640136325 10591733881945970370025561)
                ·
                  refine ⟨7943800411459477777519171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10591733881945970370025561 7943800411459477777519171)
                  ·
                    refine ⟨11915700617189216666278757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7943800411459477777519171 11915700617189216666278757)
                    ·
                      refine ⟨2234193865722978124927267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11915700617189216666278757 2234193865722978124927267)
                      ·
                        rfl

theorem cell23_4351077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4351077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351077 prefixEnd_4351077 := by exact prefixLift 4351077
  have htrace : WordTrace (prefixWord ++ tailWord_4351077) baseStart_4351077 baseEnd_4351077 := by
    simpa [prefixWord, tailWord_4351077, baseEnd_4351077] using wordTrace_append hprefix tailTrace_4351077
  have hstable : (prefixWord ++ tailWord_4351077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351077).length < 2 ^ (prefixWord ++ tailWord_4351077).sum := by decide
  have hdescent : baseEnd_4351077 < baseStart_4351077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351087 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 3, 4]
def baseStart_4351087 : Nat := 118140960795 + 4351087 * 2 ^ 59
def prefixEnd_4351087 : Nat := 4983230072969 + 3 ^ 40 * 4351087 * 2
def baseEnd_4351087 : Nat := 744733000176507695267407

theorem tailTrace_4351087 : CollatzResearch.WordTrace tailWord_4351087 prefixEnd_4351087 744733000176507695267407 := by
  unfold tailWord_4351087
  simp only [CollatzResearch.WordTrace]
  refine ⟨158697180387762380342979515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105798120258508253561986343 158697180387762380342979515)
  ·
    refine ⟨238045770581643570514469273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158697180387762380342979515 238045770581643570514469273)
    ·
      refine ⟨178534327936232677885851955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238045770581643570514469273 178534327936232677885851955)
      ·
        refine ⟨267801491904349016828777933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178534327936232677885851955 267801491904349016828777933)
        ·
          refine ⟨100425559464130881310791725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267801491904349016828777933 100425559464130881310791725)
          ·
            refine ⟨37659584799049080491546897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100425559464130881310791725 37659584799049080491546897)
            ·
              refine ⟨28244688599286810368660173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37659584799049080491546897 28244688599286810368660173)
              ·
                refine ⟨10591758224732553888247565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28244688599286810368660173 10591758224732553888247565)
                ·
                  refine ⟨3971909334274707708092837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10591758224732553888247565 3971909334274707708092837)
                  ·
                    refine ⟨744733000176507695267407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971909334274707708092837 744733000176507695267407)
                    ·
                      rfl

theorem cell23_4351087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_4351087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351087 prefixEnd_4351087 := by exact prefixLift 4351087
  have htrace : WordTrace (prefixWord ++ tailWord_4351087) baseStart_4351087 baseEnd_4351087 := by
    simpa [prefixWord, tailWord_4351087, baseEnd_4351087] using wordTrace_append hprefix tailTrace_4351087
  have hstable : (prefixWord ++ tailWord_4351087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351087).length < 2 ^ (prefixWord ++ tailWord_4351087).sum := by decide
  have hdescent : baseEnd_4351087 < baseStart_4351087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351134 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_4351134 : Nat := 118140960795 + 4351134 * 2 ^ 59
def prefixEnd_4351134 : Nat := 4983230072969 + 3 ^ 40 * 4351134 * 2
def baseEnd_4351134 : Nat := 248247014902253822434945

theorem tailTrace_4351134 : CollatzResearch.WordTrace tailWord_4351134 prefixEnd_4351134 248247014902253822434945 := by
  unfold tailWord_4351134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19837361827324013421242557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105799263079061404913293637 19837361827324013421242557)
  ·
    refine ⟨7439010685246505032965959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19837361827324013421242557 7439010685246505032965959)
    ·
      refine ⟨11158516027869757549448939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7439010685246505032965959 11158516027869757549448939)
      ·
        refine ⟨16737774041804636324173409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11158516027869757549448939 16737774041804636324173409)
        ·
          refine ⟨12553330531353477243130057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16737774041804636324173409 12553330531353477243130057)
          ·
            refine ⟨9414997898515107932347543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12553330531353477243130057 9414997898515107932347543)
            ·
              refine ⟨14122496847772661898521315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9414997898515107932347543 14122496847772661898521315)
              ·
                refine ⟨21183745271658992847781973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14122496847772661898521315 21183745271658992847781973)
                ·
                  refine ⟨248247014902253822434945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21183745271658992847781973 248247014902253822434945)
                  ·
                    rfl

theorem cell23_4351134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_4351134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351134 prefixEnd_4351134 := by exact prefixLift 4351134
  have htrace : WordTrace (prefixWord ++ tailWord_4351134) baseStart_4351134 baseEnd_4351134 := by
    simpa [prefixWord, tailWord_4351134, baseEnd_4351134] using wordTrace_append hprefix tailTrace_4351134
  have hstable : (prefixWord ++ tailWord_4351134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351134).length < 2 ^ (prefixWord ++ tailWord_4351134).sum := by decide
  have hdescent : baseEnd_4351134 < baseStart_4351134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351154 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_4351154 : Nat := 118140960795 + 4351154 * 2 ^ 59
def prefixEnd_4351154 : Nat := 4983230072969 + 3 ^ 40 * 4351154 * 2
def baseEnd_4351154 : Nat := 2234233403733374323664413

theorem tailTrace_4351154 : CollatzResearch.WordTrace tailWord_4351154 prefixEnd_4351154 2234233403733374323664413 := by
  unfold tailWord_4351154
  simp only [CollatzResearch.WordTrace]
  refine ⟨39674906019629912696417129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105799749385679767190445677 39674906019629912696417129)
  ·
    refine ⟨29756179514722434522312847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39674906019629912696417129 29756179514722434522312847)
    ·
      refine ⟨44634269272083651783469271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29756179514722434522312847 44634269272083651783469271)
      ·
        refine ⟨66951403908125477675203907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44634269272083651783469271 66951403908125477675203907)
        ·
          refine ⟨100427105862188216512805861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66951403908125477675203907 100427105862188216512805861)
          ·
            refine ⟨18830082349160290596151099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100427105862188216512805861 18830082349160290596151099)
            ·
              refine ⟨28245123523740435894226649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18830082349160290596151099 28245123523740435894226649)
              ·
                refine ⟨21183842642805326920669987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28245123523740435894226649 21183842642805326920669987)
                ·
                  refine ⟨31775763964207990381004981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21183842642805326920669987 31775763964207990381004981)
                  ·
                    refine ⟨2978977871644499098219217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31775763964207990381004981 2978977871644499098219217)
                    ·
                      refine ⟨2234233403733374323664413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2978977871644499098219217 2234233403733374323664413)
                      ·
                        rfl

theorem cell23_4351154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_4351154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351154 prefixEnd_4351154 := by exact prefixLift 4351154
  have htrace : WordTrace (prefixWord ++ tailWord_4351154) baseStart_4351154 baseEnd_4351154 := by
    simpa [prefixWord, tailWord_4351154, baseEnd_4351154] using wordTrace_append hprefix tailTrace_4351154
  have hstable : (prefixWord ++ tailWord_4351154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351154).length < 2 ^ (prefixWord ++ tailWord_4351154).sum := by decide
  have hdescent : baseEnd_4351154 < baseStart_4351154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351164 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_4351164 : Nat := 118140960795 + 4351164 * 2 ^ 59
def prefixEnd_4351164 : Nat := 4983230072969 + 3 ^ 40 * 4351164 * 2
def baseEnd_4351164 : Nat := 744746179513306428179789

theorem tailTrace_4351164 : CollatzResearch.WordTrace tailWord_4351164 prefixEnd_4351164 744746179513306428179789 := by
  unfold tailWord_4351164
  simp only [CollatzResearch.WordTrace]
  refine ⟨79349994404241711246766273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105799992538988948329021697 79349994404241711246766273)
  ·
    refine ⟨59512495803181283435074705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79349994404241711246766273 59512495803181283435074705)
    ·
      refine ⟨44634371852385962576306029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59512495803181283435074705 44634371852385962576306029)
      ·
        refine ⟨16737889444644735966114761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44634371852385962576306029 16737889444644735966114761)
        ·
          refine ⟨12553417083483551974586071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16737889444644735966114761 12553417083483551974586071)
          ·
            refine ⟨18830125625225327961879107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12553417083483551974586071 18830125625225327961879107)
            ·
              refine ⟨28245188437837991942818661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18830125625225327961879107 28245188437837991942818661)
              ·
                refine ⟨5295972832094623489278499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28245188437837991942818661 5295972832094623489278499)
                ·
                  refine ⟨7943959248141935233917749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5295972832094623489278499 7943959248141935233917749)
                  ·
                    refine ⟨744746179513306428179789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7943959248141935233917749 744746179513306428179789)
                    ·
                      rfl

theorem cell23_4351164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_4351164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351164 prefixEnd_4351164 := by exact prefixLift 4351164
  have htrace : WordTrace (prefixWord ++ tailWord_4351164) baseStart_4351164 baseEnd_4351164 := by
    simpa [prefixWord, tailWord_4351164, baseEnd_4351164] using wordTrace_append hprefix tailTrace_4351164
  have hstable : (prefixWord ++ tailWord_4351164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351164).length < 2 ^ (prefixWord ++ tailWord_4351164).sum := by decide
  have hdescent : baseEnd_4351164 < baseStart_4351164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351167 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_4351167 : Nat := 118140960795 + 4351167 * 2 ^ 59
def prefixEnd_4351167 : Nat := 4983230072969 + 3 ^ 40 * 4351167 * 2
def baseEnd_4351167 : Nat := 2234240078981882772801853

theorem tailTrace_4351167 : CollatzResearch.WordTrace tailWord_4351167 prefixEnd_4351167 2234240078981882772801853 := by
  unfold tailWord_4351167
  simp only [CollatzResearch.WordTrace]
  refine ⟨158700098227472554005891755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105800065484981702670594503 158700098227472554005891755)
  ·
    refine ⟨238050147341208831008837633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158700098227472554005891755 238050147341208831008837633)
    ·
      refine ⟨178537610505906623256628225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238050147341208831008837633 178537610505906623256628225)
      ·
        refine ⟨133903207879429967442471169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178537610505906623256628225 133903207879429967442471169)
        ·
          refine ⟨100427405909572475581853377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133903207879429967442471169 100427405909572475581853377)
          ·
            refine ⟨75320554432179356686390033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100427405909572475581853377 75320554432179356686390033)
            ·
              refine ⟨56490415824134517514792525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75320554432179356686390033 56490415824134517514792525)
              ·
                refine ⟨21183905934050444068047197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56490415824134517514792525 21183905934050444068047197)
                ·
                  refine ⟨7943964725268916525517699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21183905934050444068047197 7943964725268916525517699)
                  ·
                    refine ⟨11915947087903374788276549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7943964725268916525517699 11915947087903374788276549)
                    ·
                      refine ⟨2234240078981882772801853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11915947087903374788276549 2234240078981882772801853)
                      ·
                        rfl

theorem cell23_4351167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_4351167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351167 prefixEnd_4351167 := by exact prefixLift 4351167
  have htrace : WordTrace (prefixWord ++ tailWord_4351167) baseStart_4351167 baseEnd_4351167 := by
    simpa [prefixWord, tailWord_4351167, baseEnd_4351167] using wordTrace_append hprefix tailTrace_4351167
  have hstable : (prefixWord ++ tailWord_4351167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351167).length < 2 ^ (prefixWord ++ tailWord_4351167).sum := by decide
  have hdescent : baseEnd_4351167 < baseStart_4351167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351178 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_4351178 : Nat := 118140960795 + 4351178 * 2 ^ 59
def prefixEnd_4351178 : Nat := 4983230072969 + 3 ^ 40 * 4351178 * 2
def baseEnd_4351178 : Nat := 2234245727269082229764303

theorem tailTrace_4351178 : CollatzResearch.WordTrace tailWord_4351178 prefixEnd_4351178 2234245727269082229764303 := by
  unfold tailWord_4351178
  simp only [CollatzResearch.WordTrace]
  refine ⟨39675124857608175721135547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105800332953621801923028125 39675124857608175721135547)
  ·
    refine ⟨59512687286412263581703321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39675124857608175721135547 59512687286412263581703321)
    ·
      refine ⟨44634515464809197686277491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59512687286412263581703321 44634515464809197686277491)
      ·
        refine ⟨66951773197213796529416237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44634515464809197686277491 66951773197213796529416237)
        ·
          refine ⟨25106914948955173698531089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66951773197213796529416237 25106914948955173698531089)
          ·
            refine ⟨18830186211716380273898317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25106914948955173698531089 18830186211716380273898317)
            ·
              refine ⟨7061319829393642602711869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18830186211716380273898317 7061319829393642602711869)
              ·
                refine ⟨2647994936022615976016951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7061319829393642602711869 2647994936022615976016951)
                ·
                  refine ⟨3971992404033923964025427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647994936022615976016951 3971992404033923964025427)
                  ·
                    refine ⟨5957988606050885946038141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3971992404033923964025427 5957988606050885946038141)
                    ·
                      refine ⟨2234245727269082229764303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5957988606050885946038141 2234245727269082229764303)
                      ·
                        rfl

theorem cell23_4351178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_4351178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351178 prefixEnd_4351178 := by exact prefixLift 4351178
  have htrace : WordTrace (prefixWord ++ tailWord_4351178) baseStart_4351178 baseEnd_4351178 := by
    simpa [prefixWord, tailWord_4351178, baseEnd_4351178] using wordTrace_append hprefix tailTrace_4351178
  have hstable : (prefixWord ++ tailWord_4351178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351178).length < 2 ^ (prefixWord ++ tailWord_4351178).sum := by decide
  have hdescent : baseEnd_4351178 < baseStart_4351178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351194 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_4351194 : Nat := 118140960795 + 4351194 * 2 ^ 59
def prefixEnd_4351194 : Nat := 4983230072969 + 3 ^ 40 * 4351194 * 2
def baseEnd_4351194 : Nat := 744751314319851389054743

theorem tailTrace_4351194 : CollatzResearch.WordTrace tailWord_4351194 prefixEnd_4351194 744751314319851389054743 := by
  unfold tailWord_4351194
  simp only [CollatzResearch.WordTrace]
  refine ⟨39675270749593684404281159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105800721998916491744749757 39675270749593684404281159)
  ·
    refine ⟨59512906124390526606421739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39675270749593684404281159 59512906124390526606421739)
    ·
      refine ⟨89269359186585789909632609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59512906124390526606421739 89269359186585789909632609)
      ·
        refine ⟨66952019389939342432224457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89269359186585789909632609 66952019389939342432224457)
        ·
          refine ⟨50214014542454506824168343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66952019389939342432224457 50214014542454506824168343)
          ·
            refine ⟨75321021813681760236252515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50214014542454506824168343 75321021813681760236252515)
            ·
              refine ⟨112981532720522640354378773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75321021813681760236252515 112981532720522640354378773)
              ·
                refine ⟨5296009346274498766611505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112981532720522640354378773 5296009346274498766611505)
                ·
                  refine ⟨3972007009705874074958629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5296009346274498766611505 3972007009705874074958629)
                  ·
                    refine ⟨744751314319851389054743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972007009705874074958629 744751314319851389054743)
                    ·
                      rfl

theorem cell23_4351194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_4351194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351194 prefixEnd_4351194 := by exact prefixLift 4351194
  have htrace : WordTrace (prefixWord ++ tailWord_4351194) baseStart_4351194 baseEnd_4351194 := by
    simpa [prefixWord, tailWord_4351194, baseEnd_4351194] using wordTrace_append hprefix tailTrace_4351194
  have hstable : (prefixWord ++ tailWord_4351194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351194).length < 2 ^ (prefixWord ++ tailWord_4351194).sum := by decide
  have hdescent : baseEnd_4351194 < baseStart_4351194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351211 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 2, 4]
def baseStart_4351211 : Nat := 118140960795 + 4351211 * 2 ^ 59
def prefixEnd_4351211 : Nat := 4983230072969 + 3 ^ 40 * 4351211 * 2
def baseEnd_4351211 : Nat := 744754224043560200217217

theorem tailTrace_4351211 : CollatzResearch.WordTrace tailWord_4351211 prefixEnd_4351211 744754224043560200217217 := by
  unfold tailWord_4351211
  simp only [CollatzResearch.WordTrace]
  refine ⟨158701703039313149520493487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105801135359542099680328991 158701703039313149520493487)
  ·
    refine ⟨238052554558969724280740231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158701703039313149520493487 238052554558969724280740231)
    ·
      refine ⟨357078831838454586421110347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238052554558969724280740231 357078831838454586421110347)
      ·
        refine ⟨535618247757681879631665521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357078831838454586421110347 535618247757681879631665521)
        ·
          refine ⟨401713685818261409723749141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535618247757681879631665521 401713685818261409723749141)
          ·
            refine ⟨18830329022731003580800741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 401713685818261409723749141 18830329022731003580800741)
            ·
              refine ⟨3530686691762063171400139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18830329022731003580800741 3530686691762063171400139)
              ·
                refine ⟨5296030037643094757100209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530686691762063171400139 5296030037643094757100209)
                ·
                  refine ⟨3972022528232321067825157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5296030037643094757100209 3972022528232321067825157)
                  ·
                    refine ⟨744754224043560200217217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972022528232321067825157 744754224043560200217217)
                    ·
                      rfl

theorem cell23_4351211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 4].length) (baseStart_4351211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351211 prefixEnd_4351211 := by exact prefixLift 4351211
  have htrace : WordTrace (prefixWord ++ tailWord_4351211) baseStart_4351211 baseEnd_4351211 := by
    simpa [prefixWord, tailWord_4351211, baseEnd_4351211] using wordTrace_append hprefix tailTrace_4351211
  have hstable : (prefixWord ++ tailWord_4351211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351211).length < 2 ^ (prefixWord ++ tailWord_4351211).sum := by decide
  have hdescent : baseEnd_4351211 < baseStart_4351211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351218 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4351218 : Nat := 118140960795 + 4351218 * 2 ^ 59
def prefixEnd_4351218 : Nat := 4983230072969 + 3 ^ 40 * 4351218 * 2
def baseEnd_4351218 : Nat := 2234266266495262073264119

theorem tailTrace_4351218 : CollatzResearch.WordTrace tailWord_4351218 prefixEnd_4351218 2234266266495262073264119 := by
  unfold tailWord_4351218
  simp only [CollatzResearch.WordTrace]
  refine ⟨39675489587571947428999577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105801305566858526477332205 39675489587571947428999577)
  ·
    refine ⟨29756617190678960571749683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39675489587571947428999577 29756617190678960571749683)
    ·
      refine ⟨44634925786018440857624525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29756617190678960571749683 44634925786018440857624525)
      ·
        refine ⟨16738097169756915321609197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44634925786018440857624525 16738097169756915321609197)
        ·
          refine ⟨6276786438658843245603449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16738097169756915321609197 6276786438658843245603449)
          ·
            refine ⟨4707589828994132434202587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6276786438658843245603449 4707589828994132434202587)
            ·
              refine ⟨7061384743491198651303881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4707589828994132434202587 7061384743491198651303881)
              ·
                refine ⟨5296038557618398988477911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7061384743491198651303881 5296038557618398988477911)
                ·
                  refine ⟨7944057836427598482716867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5296038557618398988477911 7944057836427598482716867)
                  ·
                    refine ⟨11916086754641397724075301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7944057836427598482716867 11916086754641397724075301)
                    ·
                      refine ⟨2234266266495262073264119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11916086754641397724075301 2234266266495262073264119)
                      ·
                        rfl

theorem cell23_4351218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4351218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351218 prefixEnd_4351218 := by exact prefixLift 4351218
  have htrace : WordTrace (prefixWord ++ tailWord_4351218) baseStart_4351218 baseEnd_4351218 := by
    simpa [prefixWord, tailWord_4351218, baseEnd_4351218] using wordTrace_append hprefix tailTrace_4351218
  have hstable : (prefixWord ++ tailWord_4351218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351218).length < 2 ^ (prefixWord ++ tailWord_4351218).sum := by decide
  have hdescent : baseEnd_4351218 < baseStart_4351218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351267 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 8]
def baseStart_4351267 : Nat := 118140960795 + 4351267 * 2 ^ 59
def prefixEnd_4351267 : Nat := 4983230072969 + 3 ^ 40 * 4351267 * 2
def baseEnd_4351267 : Nat := 744763809015777460517131

theorem tailTrace_4351267 : CollatzResearch.WordTrace tailWord_4351267 prefixEnd_4351267 744763809015777460517131 := by
  unfold tailWord_4351267
  simp only [CollatzResearch.WordTrace]
  refine ⟨158703745527110271084532055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105802497018073514056354703 158703745527110271084532055)
  ·
    refine ⟨238055618290665406626798083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158703745527110271084532055 238055618290665406626798083)
    ·
      refine ⟨357083427435998109940197125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238055618290665406626798083 357083427435998109940197125)
      ·
        refine ⟨66953142644249645613786961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 357083427435998109940197125 66953142644249645613786961)
        ·
          refine ⟨50214856983187234210340221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66953142644249645613786961 50214856983187234210340221)
          ·
            refine ⟨18830571368695212828877583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50214856983187234210340221 18830571368695212828877583)
            ·
              refine ⟨28245857053042819243316375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18830571368695212828877583 28245857053042819243316375)
              ·
                refine ⟨42368785579564228864974563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28245857053042819243316375 42368785579564228864974563)
                ·
                  refine ⟨63553178369346343297461845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42368785579564228864974563 63553178369346343297461845)
                  ·
                    refine ⟨744763809015777460517131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63553178369346343297461845 744763809015777460517131)
                    ·
                      rfl

theorem cell23_4351267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 8].length) (baseStart_4351267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351267 prefixEnd_4351267 := by exact prefixLift 4351267
  have htrace : WordTrace (prefixWord ++ tailWord_4351267) baseStart_4351267 baseEnd_4351267 := by
    simpa [prefixWord, tailWord_4351267, baseEnd_4351267] using wordTrace_append hprefix tailTrace_4351267
  have hstable : (prefixWord ++ tailWord_4351267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351267).length < 2 ^ (prefixWord ++ tailWord_4351267).sum := by decide
  have hdescent : baseEnd_4351267 < baseStart_4351267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351284 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_4351284 : Nat := 118140960795 + 4351284 * 2 ^ 59
def prefixEnd_4351284 : Nat := 4983230072969 + 3 ^ 40 * 4351284 * 2
def baseEnd_4351284 : Nat := 744766718739486271679605

theorem tailTrace_4351284 : CollatzResearch.WordTrace tailWord_4351284 prefixEnd_4351284 744766718739486271679605 := by
  unfold tailWord_4351284
  simp only [CollatzResearch.WordTrace]
  refine ⟨79352182784024341493950453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105802910378699121991933937 79352182784024341493950453)
  ·
    refine ⟨7439267136002282015057855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79352182784024341493950453 7439267136002282015057855)
    ·
      refine ⟨11158900704003423022586783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7439267136002282015057855 11158900704003423022586783)
      ·
        refine ⟨16738351056005134533880175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11158900704003423022586783 16738351056005134533880175)
        ·
          refine ⟨25107526584007701800820263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16738351056005134533880175 25107526584007701800820263)
          ·
            refine ⟨37661289876011552701230395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25107526584007701800820263 37661289876011552701230395)
            ·
              refine ⟨56491934814017329051845593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37661289876011552701230395 56491934814017329051845593)
              ·
                refine ⟨42368951110512996788884195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56491934814017329051845593 42368951110512996788884195)
                ·
                  refine ⟨63553426665769495183326293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42368951110512996788884195 63553426665769495183326293)
                  ·
                    refine ⟨744766718739486271679605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63553426665769495183326293 744766718739486271679605)
                    ·
                      rfl

theorem cell23_4351284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_4351284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351284 prefixEnd_4351284 := by exact prefixLift 4351284
  have htrace : WordTrace (prefixWord ++ tailWord_4351284) baseStart_4351284 baseEnd_4351284 := by
    simpa [prefixWord, tailWord_4351284, baseEnd_4351284] using wordTrace_append hprefix tailTrace_4351284
  have hstable : (prefixWord ++ tailWord_4351284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351284).length < 2 ^ (prefixWord ++ tailWord_4351284).sum := by decide
  have hdescent : baseEnd_4351284 < baseStart_4351284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351294 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4351294 : Nat := 118140960795 + 4351294 * 2 ^ 59
def prefixEnd_4351294 : Nat := 4983230072969 + 3 ^ 40 * 4351294 * 2
def baseEnd_4351294 : Nat := 2234305291025003775913769

theorem tailTrace_4351294 : CollatzResearch.WordTrace tailWord_4351294 prefixEnd_4351294 2234305291025003775913769 := by
  unfold tailWord_4351294
  simp only [CollatzResearch.WordTrace]
  refine ⟨19838091287251556836970617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105803153532008303130509957 19838091287251556836970617)
  ·
    refine ⟨14878568465438667627727963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19838091287251556836970617 14878568465438667627727963)
    ·
      refine ⟨22317852698158001441591945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14878568465438667627727963 22317852698158001441591945)
      ·
        refine ⟨16738389523618501081193959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22317852698158001441591945 16738389523618501081193959)
        ·
          refine ⟨25107584285427751621790939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16738389523618501081193959 25107584285427751621790939)
          ·
            refine ⟨37661376428141627432686409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25107584285427751621790939 37661376428141627432686409)
            ·
              refine ⟨28246032321106220574514807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37661376428141627432686409 28246032321106220574514807)
              ·
                refine ⟨42369048481659330861772211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28246032321106220574514807 42369048481659330861772211)
                ·
                  refine ⟨63553572722488996292658317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42369048481659330861772211 63553572722488996292658317)
                  ·
                    refine ⟨23832589770933373609746869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63553572722488996292658317 23832589770933373609746869)
                    ·
                      refine ⟨2234305291025003775913769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23832589770933373609746869 2234305291025003775913769)
                      ·
                        rfl

theorem cell23_4351294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4351294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351294 prefixEnd_4351294 := by exact prefixLift 4351294
  have htrace : WordTrace (prefixWord ++ tailWord_4351294) baseStart_4351294 baseEnd_4351294 := by
    simpa [prefixWord, tailWord_4351294, baseEnd_4351294] using wordTrace_append hprefix tailTrace_4351294
  have hstable : (prefixWord ++ tailWord_4351294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351294).length < 2 ^ (prefixWord ++ tailWord_4351294).sum := by decide
  have hdescent : baseEnd_4351294 < baseStart_4351294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351295 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 1, 3, 2]
def baseStart_4351295 : Nat := 118140960795 + 4351295 * 2 ^ 59
def prefixEnd_4351295 : Nat := 4983230072969 + 3 ^ 40 * 4351295 * 2
def baseEnd_4351295 : Nat := 2234305804505658272001265

theorem tailTrace_4351295 : CollatzResearch.WordTrace tailWord_4351295 prefixEnd_4351295 2234305804505658272001265 := by
  unfold tailWord_4351295
  simp only [CollatzResearch.WordTrace]
  refine ⟨158704766771008831866551339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105803177847339221244367559 158704766771008831866551339)
  ·
    refine ⟨238057150156513247799827009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158704766771008831866551339 238057150156513247799827009)
    ·
      refine ⟨178542862617384935849870257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238057150156513247799827009 178542862617384935849870257)
      ·
        refine ⟨133907146963038701887402693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178542862617384935849870257 133907146963038701887402693)
        ·
          refine ⟨25107590055569756603888005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133907146963038701887402693 25107590055569756603888005)
          ·
            refine ⟨4707673135419329363229001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25107590055569756603888005 4707673135419329363229001)
            ·
              refine ⟨3530754851564497022421751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4707673135419329363229001 3530754851564497022421751)
              ·
                refine ⟨5296132277346745533632627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530754851564497022421751 5296132277346745533632627)
                ·
                  refine ⟨7944198416020118300448941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5296132277346745533632627 7944198416020118300448941)
                  ·
                    refine ⟨2979074406007544362668353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7944198416020118300448941 2979074406007544362668353)
                    ·
                      refine ⟨2234305804505658272001265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979074406007544362668353 2234305804505658272001265)
                      ·
                        rfl

theorem cell23_4351295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_4351295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351295 prefixEnd_4351295 := by exact prefixLift 4351295
  have htrace : WordTrace (prefixWord ++ tailWord_4351295) baseStart_4351295 baseEnd_4351295 := by
    simpa [prefixWord, tailWord_4351295, baseEnd_4351295] using wordTrace_append hprefix tailTrace_4351295
  have hstable : (prefixWord ++ tailWord_4351295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351295).length < 2 ^ (prefixWord ++ tailWord_4351295).sum := by decide
  have hdescent : baseEnd_4351295 < baseStart_4351295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351302 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4351302 : Nat := 118140960795 + 4351302 * 2 ^ 59
def prefixEnd_4351302 : Nat := 4983230072969 + 3 ^ 40 * 4351302 * 2
def baseEnd_4351302 : Nat := 2234309398870239744613733

theorem tailTrace_4351302 : CollatzResearch.WordTrace tailWord_4351302 prefixEnd_4351302 2234309398870239744613733 := by
  unfold tailWord_4351302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959531940061983501939255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105803348054655648041370773 4959531940061983501939255)
  ·
    refine ⟨7439297910092975252908883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4959531940061983501939255 7439297910092975252908883)
    ·
      refine ⟨11158946865139462879363325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7439297910092975252908883 11158946865139462879363325)
      ·
        refine ⟨4184605074427298579761247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11158946865139462879363325 4184605074427298579761247)
        ·
          refine ⟨6276907611640947869641871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4184605074427298579761247 6276907611640947869641871)
          ·
            refine ⟨9415361417461421804462807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6276907611640947869641871 9415361417461421804462807)
            ·
              refine ⟨14123042126192132706694211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9415361417461421804462807 14123042126192132706694211)
              ·
                refine ⟨21184563189288199060041317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14123042126192132706694211 21184563189288199060041317)
                ·
                  refine ⟨3972105597991537323757747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21184563189288199060041317 3972105597991537323757747)
                  ·
                    refine ⟨5958158396987305985636621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3972105597991537323757747 5958158396987305985636621)
                    ·
                      refine ⟨2234309398870239744613733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5958158396987305985636621 2234309398870239744613733)
                      ·
                        rfl

theorem cell23_4351302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4351302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351302 prefixEnd_4351302 := by exact prefixLift 4351302
  have htrace : WordTrace (prefixWord ++ tailWord_4351302) baseStart_4351302 baseEnd_4351302 := by
    simpa [prefixWord, tailWord_4351302, baseEnd_4351302] using wordTrace_append hprefix tailTrace_4351302
  have hstable : (prefixWord ++ tailWord_4351302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351302).length < 2 ^ (prefixWord ++ tailWord_4351302).sum := by decide
  have hdescent : baseEnd_4351302 < baseStart_4351302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351308 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4351308 : Nat := 118140960795 + 4351308 * 2 ^ 59
def prefixEnd_4351308 : Nat := 4983230072969 + 3 ^ 40 * 4351308 * 2
def baseEnd_4351308 : Nat := 2234312479754166721138705

theorem tailTrace_4351308 : CollatzResearch.WordTrace tailWord_4351308 prefixEnd_4351308 2234312479754166721138705 := by
  unfold tailWord_4351308
  simp only [CollatzResearch.WordTrace]
  refine ⟨79352620459980867543387289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105803493946641156724516385 79352620459980867543387289)
  ·
    refine ⟨59514465344985650657540467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79352620459980867543387289 59514465344985650657540467)
    ·
      refine ⟨89271698017478475986310701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59514465344985650657540467 89271698017478475986310701)
      ·
        refine ⟨33476886756554428494866513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89271698017478475986310701 33476886756554428494866513)
        ·
          refine ⟨25107665067415821371149885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33476886756554428494866513 25107665067415821371149885)
          ·
            refine ⟨9415374400280933014181207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25107665067415821371149885 9415374400280933014181207)
            ·
              refine ⟨14123061600421399521271811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9415374400280933014181207 14123061600421399521271811)
              ·
                refine ⟨21184592400632099281907717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14123061600421399521271811 21184592400632099281907717)
                ·
                  refine ⟨3972111075118518615357697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21184592400632099281907717 3972111075118518615357697)
                  ·
                    refine ⟨2979083306338888961518273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3972111075118518615357697 2979083306338888961518273)
                    ·
                      refine ⟨2234312479754166721138705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979083306338888961518273 2234312479754166721138705)
                      ·
                        rfl

theorem cell23_4351308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4351308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351308 prefixEnd_4351308 := by exact prefixLift 4351308
  have htrace : WordTrace (prefixWord ++ tailWord_4351308) baseStart_4351308 baseEnd_4351308 := by
    simpa [prefixWord, tailWord_4351308, baseEnd_4351308] using wordTrace_append hprefix tailTrace_4351308
  have hstable : (prefixWord ++ tailWord_4351308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351308).length < 2 ^ (prefixWord ++ tailWord_4351308).sum := by decide
  have hdescent : baseEnd_4351308 < baseStart_4351308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351337 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_4351337 : Nat := 118140960795 + 4351337 * 2 ^ 59
def prefixEnd_4351337 : Nat := 4983230072969 + 3 ^ 40 * 4351337 * 2
def baseEnd_4351337 : Nat := 2234327370693147107676071

theorem tailTrace_4351337 : CollatzResearch.WordTrace tailWord_4351337 prefixEnd_4351337 2234327370693147107676071 := by
  unfold tailWord_4351337
  simp only [CollatzResearch.WordTrace]
  refine ⟨158706298636856673039580265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105804199091237782026386843 158706298636856673039580265)
  ·
    refine ⟨119029723977642504779685199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158706298636856673039580265 119029723977642504779685199)
    ·
      refine ⟨178544585966463757169527799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119029723977642504779685199 178544585966463757169527799)
      ·
        refine ⟨267816878949695635754291699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178544585966463757169527799 267816878949695635754291699)
        ·
          refine ⟨401725318424543453631437549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267816878949695635754291699 401725318424543453631437549)
          ·
            refine ⟨150646994409203795111789081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401725318424543453631437549 150646994409203795111789081)
            ·
              refine ⟨112985245806902846333841811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150646994409203795111789081 112985245806902846333841811)
              ·
                refine ⟨169477868710354269500762717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112985245806902846333841811 169477868710354269500762717)
                ·
                  refine ⟨63554200766382851062786019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169477868710354269500762717 63554200766382851062786019)
                  ·
                    refine ⟨95331301149574276594179029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63554200766382851062786019 95331301149574276594179029)
                    ·
                      refine ⟨2234327370693147107676071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95331301149574276594179029 2234327370693147107676071)
                      ·
                        rfl

theorem cell23_4351337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_4351337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351337 prefixEnd_4351337 := by exact prefixLift 4351337
  have htrace : WordTrace (prefixWord ++ tailWord_4351337) baseStart_4351337 baseEnd_4351337 := by
    simpa [prefixWord, tailWord_4351337, baseEnd_4351337] using wordTrace_append hprefix tailTrace_4351337
  have hstable : (prefixWord ++ tailWord_4351337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351337).length < 2 ^ (prefixWord ++ tailWord_4351337).sum := by decide
  have hdescent : baseEnd_4351337 < baseStart_4351337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351344 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_4351344 : Nat := 118140960795 + 4351344 * 2 ^ 59
def prefixEnd_4351344 : Nat := 4983230072969 + 3 ^ 40 * 4351344 * 2
def baseEnd_4351344 : Nat := 744776988352576193429513

theorem tailTrace_4351344 : CollatzResearch.WordTrace tailWord_4351344 prefixEnd_4351344 744776988352576193429513 := by
  unfold tailWord_4351344
  simp only [CollatzResearch.WordTrace]
  refine ⟨79353276973915656617542543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105804369298554208823390057 79353276973915656617542543)
  ·
    refine ⟨119029915460873484926313815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79353276973915656617542543 119029915460873484926313815)
    ·
      refine ⟨178544873191310227389470723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119029915460873484926313815 178544873191310227389470723)
      ·
        refine ⟨267817309786965341084206085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178544873191310227389470723 267817309786965341084206085)
        ·
          refine ⟨50215745585056001453288641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267817309786965341084206085 50215745585056001453288641)
          ·
            refine ⟨37661809188792001089966481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50215745585056001453288641 37661809188792001089966481)
            ·
              refine ⟨28246356891594000817474861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37661809188792001089966481 28246356891594000817474861)
              ·
                refine ⟨10592383834347750306553073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28246356891594000817474861 10592383834347750306553073)
                ·
                  refine ⟨7944287875760812729914805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10592383834347750306553073 7944287875760812729914805)
                  ·
                    refine ⟨744776988352576193429513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7944287875760812729914805 744776988352576193429513)
                    ·
                      rfl

theorem cell23_4351344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_4351344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351344 prefixEnd_4351344 := by exact prefixLift 4351344
  have htrace : WordTrace (prefixWord ++ tailWord_4351344) baseStart_4351344 baseEnd_4351344 := by
    simpa [prefixWord, tailWord_4351344, baseEnd_4351344] using wordTrace_append hprefix tailTrace_4351344
  have hstable : (prefixWord ++ tailWord_4351344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351344).length < 2 ^ (prefixWord ++ tailWord_4351344).sum := by decide
  have hdescent : baseEnd_4351344 < baseStart_4351344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351381 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_4351381 : Nat := 118140960795 + 4351381 * 2 ^ 59
def prefixEnd_4351381 : Nat := 4983230072969 + 3 ^ 40 * 4351381 * 2
def baseEnd_4351381 : Nat := 2234349963841944935525869

theorem tailTrace_4351381 : CollatzResearch.WordTrace tailWord_4351381 prefixEnd_4351381 2234349963841944935525869 := by
  unfold tailWord_4351381
  simp only [CollatzResearch.WordTrace]
  refine ⟨158707903448697268554181997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105805268965798179036121331 158707903448697268554181997)
  ·
    refine ⟨59515463793261475707818249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158707903448697268554181997 59515463793261475707818249)
    ·
      refine ⟨44636597844946106780863687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59515463793261475707818249 44636597844946106780863687)
      ·
        refine ⟨66954896767419160171295531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44636597844946106780863687 66954896767419160171295531)
        ·
          refine ⟨100432345151128740256943297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66954896767419160171295531 100432345151128740256943297)
          ·
            refine ⟨75324258863346555192707473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100432345151128740256943297 75324258863346555192707473)
            ·
              refine ⟨56493194147509916394530605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75324258863346555192707473 56493194147509916394530605)
              ·
                refine ⟨21184947805316218647948977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56493194147509916394530605 21184947805316218647948977)
                ·
                  refine ⟨15888710853987163985961733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21184947805316218647948977 15888710853987163985961733)
                  ·
                    refine ⟨2979133285122593247367825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15888710853987163985961733 2979133285122593247367825)
                    ·
                      refine ⟨2234349963841944935525869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979133285122593247367825 2234349963841944935525869)
                      ·
                        rfl

theorem cell23_4351381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_4351381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351381 prefixEnd_4351381 := by exact prefixLift 4351381
  have htrace : WordTrace (prefixWord ++ tailWord_4351381) baseStart_4351381 baseEnd_4351381 := by
    simpa [prefixWord, tailWord_4351381, baseEnd_4351381] using wordTrace_append hprefix tailTrace_4351381
  have hstable : (prefixWord ++ tailWord_4351381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351381).length < 2 ^ (prefixWord ++ tailWord_4351381).sum := by decide
  have hdescent : baseEnd_4351381 < baseStart_4351381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351421 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 6]
def baseStart_4351421 : Nat := 118140960795 + 4351421 * 2 ^ 59
def prefixEnd_4351421 : Nat := 4983230072969 + 3 ^ 40 * 4351421 * 2
def baseEnd_4351421 : Nat := 248263389229791642113965

theorem tailTrace_4351421 : CollatzResearch.WordTrace tailWord_4351421 prefixEnd_4351421 248263389229791642113965 := by
  unfold tailWord_4351421
  simp only [CollatzResearch.WordTrace]
  refine ⟨158709362368552355385638117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105806241579034903590425411 158709362368552355385638117)
  ·
    refine ⟨29758005444103566634807147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158709362368552355385638117 29758005444103566634807147)
    ·
      refine ⟨44637008166155349952210721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29758005444103566634807147 44637008166155349952210721)
      ·
        refine ⟨33477756124616512464158041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44637008166155349952210721 33477756124616512464158041)
        ·
          refine ⟨25108317093462384348118531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33477756124616512464158041 25108317093462384348118531)
          ·
            refine ⟨37662475640193576522177797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25108317093462384348118531 37662475640193576522177797)
            ·
              refine ⟨7061714182536295597908337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37662475640193576522177797 7061714182536295597908337)
              ·
                refine ⟨5296285636902221698431253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7061714182536295597908337 5296285636902221698431253)
                ·
                  refine ⟨248263389229791642113965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5296285636902221698431253 248263389229791642113965)
                  ·
                    rfl

theorem cell23_4351421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_4351421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351421 prefixEnd_4351421 := by exact prefixLift 4351421
  have htrace : WordTrace (prefixWord ++ tailWord_4351421) baseStart_4351421 baseEnd_4351421 := by
    simpa [prefixWord, tailWord_4351421, baseEnd_4351421] using wordTrace_append hprefix tailTrace_4351421
  have hstable : (prefixWord ++ tailWord_4351421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351421).length < 2 ^ (prefixWord ++ tailWord_4351421).sum := by decide
  have hdescent : baseEnd_4351421 < baseStart_4351421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351491 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 3]
def baseStart_4351491 : Nat := 118140960795 + 4351491 * 2 ^ 59
def prefixEnd_4351491 : Nat := 4983230072969 + 3 ^ 40 * 4351491 * 2
def baseEnd_4351491 : Nat := 2234406446713939505150363

theorem tailTrace_4351491 : CollatzResearch.WordTrace tailWord_4351491 prefixEnd_4351491 2234406446713939505150363 := by
  unfold tailWord_4351491
  simp only [CollatzResearch.WordTrace]
  refine ⟨158711915478298757340686327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105807943652199171560457551 158711915478298757340686327)
  ·
    refine ⟨238067873217448136011029491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158711915478298757340686327 238067873217448136011029491)
    ·
      refine ⟨357101809826172204016544237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238067873217448136011029491 357101809826172204016544237)
      ·
        refine ⟨133913178684814576506204089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 357101809826172204016544237 133913178684814576506204089)
        ·
          refine ⟨100434884013610932379653067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133913178684814576506204089 100434884013610932379653067)
          ·
            refine ⟨150652326020416398569479601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100434884013610932379653067 150652326020416398569479601)
            ·
              refine ⟨112989244515312298927109701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150652326020416398569479601 112989244515312298927109701)
              ·
                refine ⟨21185483346621056048833069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112989244515312298927109701 21185483346621056048833069)
                ·
                  refine ⟨7944556254982896018312401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21185483346621056048833069 7944556254982896018312401)
                  ·
                    refine ⟨5958417191237172013734301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7944556254982896018312401 5958417191237172013734301)
                    ·
                      refine ⟨2234406446713939505150363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5958417191237172013734301 2234406446713939505150363)
                      ·
                        rfl

theorem cell23_4351491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_4351491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351491 prefixEnd_4351491 := by exact prefixLift 4351491
  have htrace : WordTrace (prefixWord ++ tailWord_4351491) baseStart_4351491 baseEnd_4351491 := by
    simpa [prefixWord, tailWord_4351491, baseEnd_4351491] using wordTrace_append hprefix tailTrace_4351491
  have hstable : (prefixWord ++ tailWord_4351491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351491).length < 2 ^ (prefixWord ++ tailWord_4351491).sum := by decide
  have hdescent : baseEnd_4351491 < baseStart_4351491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351498 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_4351498 : Nat := 118140960795 + 4351498 * 2 ^ 59
def prefixEnd_4351498 : Nat := 4983230072969 + 3 ^ 40 * 4351498 * 2
def baseEnd_4351498 : Nat := 744803347026173659254277

theorem tailTrace_4351498 : CollatzResearch.WordTrace tailWord_4351498 prefixEnd_4351498 744803347026173659254277 := by
  unfold tailWord_4351498
  simp only [CollatzResearch.WordTrace]
  refine ⟨39678042697318349384047787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105808113859515598357460765 39678042697318349384047787)
  ·
    refine ⟨59517064045977524076071681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39678042697318349384047787 59517064045977524076071681)
    ·
      refine ⟨44637798034483143057053761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59517064045977524076071681 44637798034483143057053761)
      ·
        refine ⟨33478348525862357292790321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44637798034483143057053761 33478348525862357292790321)
        ·
          refine ⟨25108761394396767969592741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33478348525862357292790321 25108761394396767969592741)
          ·
            refine ⟨4707892761449393994298639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25108761394396767969592741 4707892761449393994298639)
            ·
              refine ⟨7061839142174090991447959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4707892761449393994298639 7061839142174090991447959)
              ·
                refine ⟨10592758713261136487171939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7061839142174090991447959 10592758713261136487171939)
                ·
                  refine ⟨15889138069891704730757909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10592758713261136487171939 15889138069891704730757909)
                  ·
                    refine ⟨744803347026173659254277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15889138069891704730757909 744803347026173659254277)
                    ·
                      rfl

theorem cell23_4351498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_4351498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351498 prefixEnd_4351498 := by exact prefixLift 4351498
  have htrace : WordTrace (prefixWord ++ tailWord_4351498) baseStart_4351498 baseEnd_4351498 := by
    simpa [prefixWord, tailWord_4351498, baseEnd_4351498] using wordTrace_append hprefix tailTrace_4351498
  have hstable : (prefixWord ++ tailWord_4351498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351498).length < 2 ^ (prefixWord ++ tailWord_4351498).sum := by decide
  have hdescent : baseEnd_4351498 < baseStart_4351498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351528 : List Nat := [2, 1, 5, 2, 2, 2, 9]
def baseStart_4351528 : Nat := 118140960795 + 4351528 * 2 ^ 59
def prefixEnd_4351528 : Nat := 4983230072969 + 3 ^ 40 * 4351528 * 2
def baseEnd_4351528 : Nat := 27585499327137726671453

theorem tailTrace_4351528 : CollatzResearch.WordTrace tailWord_4351528 prefixEnd_4351528 27585499327137726671453 := by
  unfold tailWord_4351528
  simp only [CollatzResearch.WordTrace]
  refine ⟨79356632489582356329891619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105808843319443141773188825 79356632489582356329891619)
  ·
    refine ⟨119034948734373534494837429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79356632489582356329891619 119034948734373534494837429)
    ·
      refine ⟨11159526443847518858891009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119034948734373534494837429 11159526443847518858891009)
      ·
        refine ⟨8369644832885639144168257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11159526443847518858891009 8369644832885639144168257)
        ·
          refine ⟨6277233624664229358126193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8369644832885639144168257 6277233624664229358126193)
          ·
            refine ⟨4707925218498172018594645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6277233624664229358126193 4707925218498172018594645)
            ·
              refine ⟨27585499327137726671453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4707925218498172018594645 27585499327137726671453)
              ·
                rfl

theorem cell23_4351528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 9].length) (baseStart_4351528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351528 prefixEnd_4351528 := by exact prefixLift 4351528
  have htrace : WordTrace (prefixWord ++ tailWord_4351528) baseStart_4351528 baseEnd_4351528 := by
    simpa [prefixWord, tailWord_4351528, baseEnd_4351528] using wordTrace_append hprefix tailTrace_4351528
  have hstable : (prefixWord ++ tailWord_4351528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351528).length < 2 ^ (prefixWord ++ tailWord_4351528).sum := by decide
  have hdescent : baseEnd_4351528 < baseStart_4351528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351539 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 1, 2, 2]
def baseStart_4351539 : Nat := 118140960795 + 4351539 * 2 ^ 59
def prefixEnd_4351539 : Nat := 4983230072969 + 3 ^ 40 * 4351539 * 2
def baseEnd_4351539 : Nat := 2234431093785355317350143

theorem tailTrace_4351539 : CollatzResearch.WordTrace tailWord_4351539 prefixEnd_4351539 2234431093785355317350143 := by
  unfold tailWord_4351539
  simp only [CollatzResearch.WordTrace]
  refine ⟨158713666182124861538433671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105809110788083241025622447 158713666182124861538433671)
  ·
    refine ⟨238070499273187292307650507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158713666182124861538433671 238070499273187292307650507)
    ·
      refine ⟨357105748909780938461475761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238070499273187292307650507 357105748909780938461475761)
      ·
        refine ⟨267829311682335703846106821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357105748909780938461475761 267829311682335703846106821)
        ·
          refine ⟨50217995940437944471145029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267829311682335703846106821 50217995940437944471145029)
          ·
            refine ⟨9415874238832114588339693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50217995940437944471145029 9415874238832114588339693)
            ·
              refine ⟨3530952839562042970627385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9415874238832114588339693 3530952839562042970627385)
              ·
                refine ⟨2648214629671532227970539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3530952839562042970627385 2648214629671532227970539)
                ·
                  refine ⟨3972321944507298341955809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648214629671532227970539 3972321944507298341955809)
                  ·
                    refine ⟨2979241458380473756466857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3972321944507298341955809 2979241458380473756466857)
                    ·
                      refine ⟨2234431093785355317350143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979241458380473756466857 2234431093785355317350143)
                      ·
                        rfl

theorem cell23_4351539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 1, 2, 2].length) (baseStart_4351539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351539 prefixEnd_4351539 := by exact prefixLift 4351539
  have htrace : WordTrace (prefixWord ++ tailWord_4351539) baseStart_4351539 baseEnd_4351539 := by
    simpa [prefixWord, tailWord_4351539, baseEnd_4351539] using wordTrace_append hprefix tailTrace_4351539
  have hstable : (prefixWord ++ tailWord_4351539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351539).length < 2 ^ (prefixWord ++ tailWord_4351539).sum := by decide
  have hdescent : baseEnd_4351539 < baseStart_4351539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351549 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_4351549 : Nat := 118140960795 + 4351549 * 2 ^ 59
def prefixEnd_4351549 : Nat := 4983230072969 + 3 ^ 40 * 4351549 * 2
def baseEnd_4351549 : Nat := 744812076197300092741699

theorem tailTrace_4351549 : CollatzResearch.WordTrace tailWord_4351549 prefixEnd_4351549 744812076197300092741699 := by
  unfold tailWord_4351549
  simp only [CollatzResearch.WordTrace]
  refine ⟨158714030912088633246297701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105809353941392422164198467 158714030912088633246297701)
  ·
    refine ⟨29758880796016618733680819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158714030912088633246297701 29758880796016618733680819)
    ·
      refine ⟨44638321194024928100521229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29758880796016618733680819 44638321194024928100521229)
      ·
        refine ⟨16739370447759348037695461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44638321194024928100521229 16739370447759348037695461)
        ·
          refine ⟨3138631958954877757067899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16739370447759348037695461 3138631958954877757067899)
          ·
            refine ⟨4707947938432316635601849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138631958954877757067899 4707947938432316635601849)
            ·
              refine ⟨3530960953824237476701387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4707947938432316635601849 3530960953824237476701387)
              ·
                refine ⟨5296441430736356215052081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530960953824237476701387 5296441430736356215052081)
                ·
                  refine ⟨3972331073052267161289061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5296441430736356215052081 3972331073052267161289061)
                  ·
                    refine ⟨744812076197300092741699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972331073052267161289061 744812076197300092741699)
                    ·
                      rfl

theorem cell23_4351549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_4351549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351549 prefixEnd_4351549 := by exact prefixLift 4351549
  have htrace : WordTrace (prefixWord ++ tailWord_4351549) baseStart_4351549 baseEnd_4351549 := by
    simpa [prefixWord, tailWord_4351549, baseEnd_4351549] using wordTrace_append hprefix tailTrace_4351549
  have hstable : (prefixWord ++ tailWord_4351549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351549).length < 2 ^ (prefixWord ++ tailWord_4351549).sum := by decide
  have hdescent : baseEnd_4351549 < baseStart_4351549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351641 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_4351641 : Nat := 118140960795 + 4351641 * 2 ^ 59
def prefixEnd_4351641 : Nat := 4983230072969 + 3 ^ 40 * 4351641 * 2
def baseEnd_4351641 : Nat := 2234483468812113918274673

theorem tailTrace_4351641 : CollatzResearch.WordTrace tailWord_4351641 prefixEnd_4351641 2234483468812113918274673 := by
  unfold tailWord_4351641
  simp only [CollatzResearch.WordTrace]
  refine ⟨158717386427755332958646777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105811590951836888639097851 158717386427755332958646777)
  ·
    refine ⟨119038039820816499718985083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158717386427755332958646777 119038039820816499718985083)
    ·
      refine ⟨178557059731224749578477625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119038039820816499718985083 178557059731224749578477625)
      ·
        refine ⟨133917794798418562183858219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178557059731224749578477625 133917794798418562183858219)
        ·
          refine ⟨200876692197627843275787329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133917794798418562183858219 200876692197627843275787329)
          ·
            refine ⟨150657519148220882456840497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200876692197627843275787329 150657519148220882456840497)
            ·
              refine ⟨112993139361165661842630373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150657519148220882456840497 112993139361165661842630373)
              ·
                refine ⟨21186213630218561595493195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112993139361165661842630373 21186213630218561595493195)
                ·
                  refine ⟨31779320445327842393239793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21186213630218561595493195 31779320445327842393239793)
                  ·
                    refine ⟨23834490333995881794929845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31779320445327842393239793 23834490333995881794929845)
                    ·
                      refine ⟨2234483468812113918274673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23834490333995881794929845 2234483468812113918274673)
                      ·
                        rfl

theorem cell23_4351641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_4351641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351641 prefixEnd_4351641 := by exact prefixLift 4351641
  have htrace : WordTrace (prefixWord ++ tailWord_4351641) baseStart_4351641 baseEnd_4351641 := by
    simpa [prefixWord, tailWord_4351641, baseEnd_4351641] using wordTrace_append hprefix tailTrace_4351641
  have hstable : (prefixWord ++ tailWord_4351641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351641).length < 2 ^ (prefixWord ++ tailWord_4351641).sum := by decide
  have hdescent : baseEnd_4351641 < baseStart_4351641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351646 : List Nat := [4, 3, 1, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_4351646 : Nat := 118140960795 + 4351646 * 2 ^ 59
def prefixEnd_4351646 : Nat := 4983230072969 + 3 ^ 40 * 4351646 * 2
def baseEnd_4351646 : Nat := 2234486036215386398712151

theorem tailTrace_4351646 : CollatzResearch.WordTrace tailWord_4351646 prefixEnd_4351646 2234486036215386398712151 := by
  unfold tailWord_4351646
  simp only [CollatzResearch.WordTrace]
  refine ⟨19839696099092152351572349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105811712528491479208385861 19839696099092152351572349)
  ·
    refine ⟨7439886037159557131839631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19839696099092152351572349 7439886037159557131839631)
    ·
      refine ⟨11159829055739335697759447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7439886037159557131839631 11159829055739335697759447)
      ·
        refine ⟨16739743583609003546639171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11159829055739335697759447 16739743583609003546639171)
        ·
          refine ⟨25109615375413505319958757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16739743583609003546639171 25109615375413505319958757)
          ·
            refine ⟨4708052882890032247492267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25109615375413505319958757 4708052882890032247492267)
            ·
              refine ⟨7062079324335048371238401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708052882890032247492267 7062079324335048371238401)
              ·
                refine ⟨5296559493251286278428801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7062079324335048371238401 5296559493251286278428801)
                ·
                  refine ⟨3972419619938464708821601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5296559493251286278428801 3972419619938464708821601)
                  ·
                    refine ⟨2979314714953848531616201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3972419619938464708821601 2979314714953848531616201)
                    ·
                      refine ⟨2234486036215386398712151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979314714953848531616201 2234486036215386398712151)
                      ·
                        rfl

theorem cell23_4351646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_4351646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351646 prefixEnd_4351646 := by exact prefixLift 4351646
  have htrace : WordTrace (prefixWord ++ tailWord_4351646) baseStart_4351646 baseEnd_4351646 := by
    simpa [prefixWord, tailWord_4351646, baseEnd_4351646] using wordTrace_append hprefix tailTrace_4351646
  have hstable : (prefixWord ++ tailWord_4351646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351646).length < 2 ^ (prefixWord ++ tailWord_4351646).sum := by decide
  have hdescent : baseEnd_4351646 < baseStart_4351646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351686 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_4351686 : Nat := 118140960795 + 4351686 * 2 ^ 59
def prefixEnd_4351686 : Nat := 4983230072969 + 3 ^ 40 * 4351686 * 2
def baseEnd_4351686 : Nat := 248278508382396249134663

theorem tailTrace_4351686 : CollatzResearch.WordTrace tailWord_4351686 prefixEnd_4351686 248278508382396249134663 := by
  unfold tailWord_4351686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959969616018509551376091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105812685141728203762689941 4959969616018509551376091)
  ·
    refine ⟨7439954424027764327064137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4959969616018509551376091 7439954424027764327064137)
    ·
      refine ⟨5579965818020823245298103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7439954424027764327064137 5579965818020823245298103)
      ·
        refine ⟨8369948727031234867947155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5579965818020823245298103 8369948727031234867947155)
        ·
          refine ⟨12554923090546852301920733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8369948727031234867947155 12554923090546852301920733)
          ·
            refine ⟨4708096158955069613220275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12554923090546852301920733 4708096158955069613220275)
            ·
              refine ⟨7062144238432604419830413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708096158955069613220275 7062144238432604419830413)
              ·
                refine ⟨2648304089412226657436405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7062144238432604419830413 2648304089412226657436405)
                ·
                  refine ⟨248278508382396249134663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2648304089412226657436405 248278508382396249134663)
                  ·
                    rfl

theorem cell23_4351686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_4351686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351686 prefixEnd_4351686 := by exact prefixLift 4351686
  have htrace : WordTrace (prefixWord ++ tailWord_4351686) baseStart_4351686 baseEnd_4351686 := by
    simpa [prefixWord, tailWord_4351686, baseEnd_4351686] using wordTrace_append hprefix tailTrace_4351686
  have hstable : (prefixWord ++ tailWord_4351686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351686).length < 2 ^ (prefixWord ++ tailWord_4351686).sum := by decide
  have hdescent : baseEnd_4351686 < baseStart_4351686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351688 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 1, 4, 3]
def baseStart_4351688 : Nat := 118140960795 + 4351688 * 2 ^ 59
def prefixEnd_4351688 : Nat := 4983230072969 + 3 ^ 40 * 4351688 * 2
def baseEnd_4351688 : Nat := 2234507602402875234386957

theorem tailTrace_4351688 : CollatzResearch.WordTrace tailWord_4351688 prefixEnd_4351688 2234507602402875234386957 := by
  unfold tailWord_4351688
  simp only [CollatzResearch.WordTrace]
  refine ⟨79359550329292529992803859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105812733772390039990405145 79359550329292529992803859)
  ·
    refine ⟨119039325493938794989205789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79359550329292529992803859 119039325493938794989205789)
    ·
      refine ⟨44639747060227048120952171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119039325493938794989205789 44639747060227048120952171)
      ·
        refine ⟨66959620590340572181428257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44639747060227048120952171 66959620590340572181428257)
        ·
          refine ⟨50219715442755429136071193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66959620590340572181428257 50219715442755429136071193)
          ·
            refine ⟨37664786582066571852053395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50219715442755429136071193 37664786582066571852053395)
            ·
              refine ⟨56497179873099857778080093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37664786582066571852053395 56497179873099857778080093)
              ·
                refine ⟨21186442452412446666780035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56497179873099857778080093 21186442452412446666780035)
                ·
                  refine ⟨31779663678618670000170053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21186442452412446666780035 31779663678618670000170053)
                  ·
                    refine ⟨5958686939741000625031885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31779663678618670000170053 5958686939741000625031885)
                    ·
                      refine ⟨2234507602402875234386957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5958686939741000625031885 2234507602402875234386957)
                      ·
                        rfl

theorem cell23_4351688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_4351688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351688 prefixEnd_4351688 := by exact prefixLift 4351688
  have htrace : WordTrace (prefixWord ++ tailWord_4351688) baseStart_4351688 baseEnd_4351688 := by
    simpa [prefixWord, tailWord_4351688, baseEnd_4351688] using wordTrace_append hprefix tailTrace_4351688
  have hstable : (prefixWord ++ tailWord_4351688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351688).length < 2 ^ (prefixWord ++ tailWord_4351688).sum := by decide
  have hdescent : baseEnd_4351688 < baseStart_4351688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351705 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_4351705 : Nat := 118140960795 + 4351705 * 2 ^ 59
def prefixEnd_4351705 : Nat := 4983230072969 + 3 ^ 40 * 4351705 * 2
def baseEnd_4351705 : Nat := 2234516331574001667874379

theorem tailTrace_4351705 : CollatzResearch.WordTrace tailWord_4351705 prefixEnd_4351705 2234516331574001667874379 := by
  unfold tailWord_4351705
  simp only [CollatzResearch.WordTrace]
  refine ⟨158719720699523471888976569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105813147133015647925984379 158719720699523471888976569)
  ·
    refine ⟨119039790524642603916732427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158719720699523471888976569 119039790524642603916732427)
    ·
      refine ⟨178559685786963905875098641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119039790524642603916732427 178559685786963905875098641)
      ·
        refine ⟨133919764340222929406323981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178559685786963905875098641 133919764340222929406323981)
        ·
          refine ⟨50219911627583598527371493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133919764340222929406323981 50219911627583598527371493)
          ·
            refine ⟨9416233430171924723882155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50219911627583598527371493 9416233430171924723882155)
            ·
              refine ⟨14124350145257887085823233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9416233430171924723882155 14124350145257887085823233)
              ·
                refine ⟨10593262608943415314367425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14124350145257887085823233 10593262608943415314367425)
                ·
                  refine ⟨7944946956707561485775569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10593262608943415314367425 7944946956707561485775569)
                  ·
                    refine ⟨5958710217530671114331677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7944946956707561485775569 5958710217530671114331677)
                    ·
                      refine ⟨2234516331574001667874379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5958710217530671114331677 2234516331574001667874379)
                      ·
                        rfl

theorem cell23_4351705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_4351705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351705 prefixEnd_4351705 := by exact prefixLift 4351705
  have htrace : WordTrace (prefixWord ++ tailWord_4351705) baseStart_4351705 baseEnd_4351705 := by
    simpa [prefixWord, tailWord_4351705, baseEnd_4351705] using wordTrace_append hprefix tailTrace_4351705
  have hstable : (prefixWord ++ tailWord_4351705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351705).length < 2 ^ (prefixWord ++ tailWord_4351705).sum := by decide
  have hdescent : baseEnd_4351705 < baseStart_4351705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351721 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_4351721 : Nat := 118140960795 + 4351721 * 2 ^ 59
def prefixEnd_4351721 : Nat := 4983230072969 + 3 ^ 40 * 4351721 * 2
def baseEnd_4351721 : Nat := 744841515754824535091435

theorem tailTrace_4351721 : CollatzResearch.WordTrace tailWord_4351721 prefixEnd_4351721 744841515754824535091435 := by
  unfold tailWord_4351721
  simp only [CollatzResearch.WordTrace]
  refine ⟨158720304267465506621559017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105813536178310337747706011 158720304267465506621559017)
  ·
    refine ⟨119040228200599129966169263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158720304267465506621559017 119040228200599129966169263)
    ·
      refine ⟨178560342300898694949253895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119040228200599129966169263 178560342300898694949253895)
      ·
        refine ⟨267840513451348042423880843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178560342300898694949253895 267840513451348042423880843)
        ·
          refine ⟨401760770177022063635821265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267840513451348042423880843 401760770177022063635821265)
          ·
            refine ⟨301320577632766547726865949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401760770177022063635821265 301320577632766547726865949)
            ·
              refine ⟨112995216612287455397574731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301320577632766547726865949 112995216612287455397574731)
              ·
                refine ⟨169492824918431183096362097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112995216612287455397574731 169492824918431183096362097)
                ·
                  refine ⟨127119618688823387322271573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169492824918431183096362097 127119618688823387322271573)
                  ·
                    refine ⟨744841515754824535091435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127119618688823387322271573 744841515754824535091435)
                    ·
                      rfl

theorem cell23_4351721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_4351721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351721 prefixEnd_4351721 := by exact prefixLift 4351721
  have htrace : WordTrace (prefixWord ++ tailWord_4351721) baseStart_4351721 baseEnd_4351721 := by
    simpa [prefixWord, tailWord_4351721, baseEnd_4351721] using wordTrace_append hprefix tailTrace_4351721
  have hstable : (prefixWord ++ tailWord_4351721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351721).length < 2 ^ (prefixWord ++ tailWord_4351721).sum := by decide
  have hdescent : baseEnd_4351721 < baseStart_4351721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351725 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 6]
def baseStart_4351725 : Nat := 118140960795 + 4351725 * 2 ^ 59
def prefixEnd_4351725 : Nat := 4983230072969 + 3 ^ 40 * 4351725 * 2
def baseEnd_4351725 : Nat := 248280733465232398847143

theorem tailTrace_4351725 : CollatzResearch.WordTrace tailWord_4351725 prefixEnd_4351725 248280733465232398847143 := by
  unfold tailWord_4351725
  simp only [CollatzResearch.WordTrace]
  refine ⟨158720450159451015304704629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105813633439634010203136419 158720450159451015304704629)
  ·
    refine ⟨14880042202448532684816059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 158720450159451015304704629 14880042202448532684816059)
    ·
      refine ⟨22320063303672799027224089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14880042202448532684816059 22320063303672799027224089)
      ·
        refine ⟨16740047477754599270418067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22320063303672799027224089 16740047477754599270418067)
        ·
          refine ⟨25110071216631898905627101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16740047477754599270418067 25110071216631898905627101)
          ·
            refine ⟨9416276706236962089610163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25110071216631898905627101 9416276706236962089610163)
            ·
              refine ⟨14124415059355443134415245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9416276706236962089610163 14124415059355443134415245)
              ·
                refine ⟨5296655647258291175405717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14124415059355443134415245 5296655647258291175405717)
                ·
                  refine ⟨248280733465232398847143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5296655647258291175405717 248280733465232398847143)
                  ·
                    rfl

theorem cell23_4351725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_4351725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351725 prefixEnd_4351725 := by exact prefixLift 4351725
  have htrace : WordTrace (prefixWord ++ tailWord_4351725) baseStart_4351725 baseEnd_4351725 := by
    simpa [prefixWord, tailWord_4351725, baseEnd_4351725] using wordTrace_append hprefix tailTrace_4351725
  have hstable : (prefixWord ++ tailWord_4351725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351725).length < 2 ^ (prefixWord ++ tailWord_4351725).sum := by decide
  have hdescent : baseEnd_4351725 < baseStart_4351725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351735 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_4351735 : Nat := 118140960795 + 4351735 * 2 ^ 59
def prefixEnd_4351735 : Nat := 4983230072969 + 3 ^ 40 * 4351735 * 2
def baseEnd_4351735 : Nat := 2234531735993636550499241

theorem tailTrace_4351735 : CollatzResearch.WordTrace tailWord_4351735 prefixEnd_4351735 2234531735993636550499241 := by
  unfold tailWord_4351735
  simp only [CollatzResearch.WordTrace]
  refine ⟨158720814889414787012568659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105813876592943191341712439 158720814889414787012568659)
  ·
    refine ⟨238081222334122180518852989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158720814889414787012568659 238081222334122180518852989)
    ·
      refine ⟨89280458375295817694569871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238081222334122180518852989 89280458375295817694569871)
      ·
        refine ⟨133920687562943726541854807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89280458375295817694569871 133920687562943726541854807)
        ·
          refine ⟨200881031344415589812782211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133920687562943726541854807 200881031344415589812782211)
          ·
            refine ⟨301321547016623384719173317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200881031344415589812782211 301321547016623384719173317)
            ·
              refine ⟨56497790065616884634844997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301321547016623384719173317 56497790065616884634844997)
              ·
                refine ⟨10593335637303165869033437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56497790065616884634844997 10593335637303165869033437)
                ·
                  refine ⟨3972500863988687200887539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10593335637303165869033437 3972500863988687200887539)
                  ·
                    refine ⟨5958751295983030801331309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3972500863988687200887539 5958751295983030801331309)
                    ·
                      refine ⟨2234531735993636550499241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5958751295983030801331309 2234531735993636550499241)
                      ·
                        rfl

theorem cell23_4351735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_4351735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351735 prefixEnd_4351735 := by exact prefixLift 4351735
  have htrace : WordTrace (prefixWord ++ tailWord_4351735) baseStart_4351735 baseEnd_4351735 := by
    simpa [prefixWord, tailWord_4351735, baseEnd_4351735] using wordTrace_append hprefix tailTrace_4351735
  have hstable : (prefixWord ++ tailWord_4351735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351735).length < 2 ^ (prefixWord ++ tailWord_4351735).sum := by decide
  have hdescent : baseEnd_4351735 < baseStart_4351735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351745 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_4351745 : Nat := 118140960795 + 4351745 * 2 ^ 59
def prefixEnd_4351745 : Nat := 4983230072969 + 3 ^ 40 * 4351745 * 2
def baseEnd_4351745 : Nat := 2234536870800181511374195

theorem tailTrace_4351745 : CollatzResearch.WordTrace tailWord_4351745 prefixEnd_4351745 2234536870800181511374195 := by
  unfold tailWord_4351745
  simp only [CollatzResearch.WordTrace]
  refine ⟨158721179619378558720432689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105814119746252372480288459 158721179619378558720432689)
  ·
    refine ⟨119040884714533919040324517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158721179619378558720432689 119040884714533919040324517)
    ·
      refine ⟨22320165883975109820060847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119040884714533919040324517 22320165883975109820060847)
      ·
        refine ⟨33480248825962664730091271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22320165883975109820060847 33480248825962664730091271)
        ·
          refine ⟨50220373238943997095136907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33480248825962664730091271 50220373238943997095136907)
          ·
            refine ⟨75330559858415995642705361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50220373238943997095136907 75330559858415995642705361)
            ·
              refine ⟨56497919893811996732029021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75330559858415995642705361 56497919893811996732029021)
              ·
                refine ⟨21186719960179498774510883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56497919893811996732029021 21186719960179498774510883)
                ·
                  refine ⟨31780079940269248161766325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21186719960179498774510883 31780079940269248161766325)
                  ·
                    refine ⟨2979382494400242015165593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31780079940269248161766325 2979382494400242015165593)
                    ·
                      refine ⟨2234536870800181511374195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979382494400242015165593 2234536870800181511374195)
                      ·
                        rfl

theorem cell23_4351745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_4351745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351745 prefixEnd_4351745 := by exact prefixLift 4351745
  have htrace : WordTrace (prefixWord ++ tailWord_4351745) baseStart_4351745 baseEnd_4351745 := by
    simpa [prefixWord, tailWord_4351745, baseEnd_4351745] using wordTrace_append hprefix tailTrace_4351745
  have hstable : (prefixWord ++ tailWord_4351745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351745).length < 2 ^ (prefixWord ++ tailWord_4351745).sum := by decide
  have hdescent : baseEnd_4351745 < baseStart_4351745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351796 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_4351796 : Nat := 118140960795 + 4351796 * 2 ^ 59
def prefixEnd_4351796 : Nat := 4983230072969 + 3 ^ 40 * 4351796 * 2
def baseEnd_4351796 : Nat := 2234563058313560811836461

theorem tailTrace_4351796 : CollatzResearch.WordTrace tailWord_4351796 prefixEnd_4351796 2234563058313560811836461 := by
  unfold tailWord_4351796
  simp only [CollatzResearch.WordTrace]
  refine ⟨79361519871096897215269621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105815359828129196287026161 79361519871096897215269621)
  ·
    refine ⟨7440142487915334113931527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79361519871096897215269621 7440142487915334113931527)
    ·
      refine ⟨11160213731873001170897291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7440142487915334113931527 11160213731873001170897291)
      ·
        refine ⟨16740320597809501756345937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11160213731873001170897291 16740320597809501756345937)
        ·
          refine ⟨12555240448357126317259453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16740320597809501756345937 12555240448357126317259453)
          ·
            refine ⟨4708215168133922368972295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12555240448357126317259453 4708215168133922368972295)
            ·
              refine ⟨7062322752200883553458443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708215168133922368972295 7062322752200883553458443)
              ·
                refine ⟨10593484128301325330187665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7062322752200883553458443 10593484128301325330187665)
                ·
                  refine ⟨7945113096225993997640749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10593484128301325330187665 7945113096225993997640749)
                  ·
                    refine ⟨2979417411084747749115281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945113096225993997640749 2979417411084747749115281)
                    ·
                      refine ⟨2234563058313560811836461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979417411084747749115281 2234563058313560811836461)
                      ·
                        rfl

theorem cell23_4351796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_4351796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351796 prefixEnd_4351796 := by exact prefixLift 4351796
  have htrace : WordTrace (prefixWord ++ tailWord_4351796) baseStart_4351796 baseEnd_4351796 := by
    simpa [prefixWord, tailWord_4351796, baseEnd_4351796] using wordTrace_append hprefix tailTrace_4351796
  have hstable : (prefixWord ++ tailWord_4351796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351796).length < 2 ^ (prefixWord ++ tailWord_4351796).sum := by decide
  have hdescent : baseEnd_4351796 < baseStart_4351796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351826 : List Nat := [3, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_4351826 : Nat := 118140960795 + 4351826 * 2 ^ 59
def prefixEnd_4351826 : Nat := 4983230072969 + 3 ^ 40 * 4351826 * 2
def baseEnd_4351826 : Nat := 2234578462733195694461323

theorem tailTrace_4351826 : CollatzResearch.WordTrace tailWord_4351826 prefixEnd_4351826 2234578462733195694461323 := by
  unfold tailWord_4351826
  simp only [CollatzResearch.WordTrace]
  refine ⟨39681033483021277388532833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105816089288056739702754221 39681033483021277388532833)
  ·
    refine ⟨29760775112265958041399625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39681033483021277388532833 29760775112265958041399625)
    ·
      refine ⟨22320581334199468531049719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29760775112265958041399625 22320581334199468531049719)
      ·
        refine ⟨33480872001299202796574579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22320581334199468531049719 33480872001299202796574579)
        ·
          refine ⟨50221308001948804194861869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33480872001299202796574579 50221308001948804194861869)
          ·
            refine ⟨18832990500730801573073201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50221308001948804194861869 18832990500730801573073201)
            ·
              refine ⟨14124742875548101179804901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18832990500730801573073201 14124742875548101179804901)
              ·
                refine ⟨2648389289165268971213419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14124742875548101179804901 2648389289165268971213419)
                ·
                  refine ⟨3972583933747903456820129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648389289165268971213419 3972583933747903456820129)
                  ·
                    refine ⟨2979437950310927592615097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3972583933747903456820129 2979437950310927592615097)
                    ·
                      refine ⟨2234578462733195694461323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979437950310927592615097 2234578462733195694461323)
                      ·
                        rfl

theorem cell23_4351826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_4351826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351826 prefixEnd_4351826 := by exact prefixLift 4351826
  have htrace : WordTrace (prefixWord ++ tailWord_4351826) baseStart_4351826 baseEnd_4351826 := by
    simpa [prefixWord, tailWord_4351826, baseEnd_4351826] using wordTrace_append hprefix tailTrace_4351826
  have hstable : (prefixWord ++ tailWord_4351826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351826).length < 2 ^ (prefixWord ++ tailWord_4351826).sum := by decide
  have hdescent : baseEnd_4351826 < baseStart_4351826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351836 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_4351836 : Nat := 118140960795 + 4351836 * 2 ^ 59
def prefixEnd_4351836 : Nat := 4983230072969 + 3 ^ 40 * 4351836 * 2
def baseEnd_4351836 : Nat := 744861199179913551778759

theorem tailTrace_4351836 : CollatzResearch.WordTrace tailWord_4351836 prefixEnd_4351836 744861199179913551778759 := by
  unfold tailWord_4351836
  simp only [CollatzResearch.WordTrace]
  refine ⟨79362249331024440630997681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105816332441365920841330241 79362249331024440630997681)
  ·
    refine ⟨59521686998268330473248261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79362249331024440630997681 59521686998268330473248261)
    ·
      refine ⟨11160316312175311963734049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59521686998268330473248261 11160316312175311963734049)
      ·
        refine ⟨8370237234131483972800537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11160316312175311963734049 8370237234131483972800537)
        ·
          refine ⟨6277677925598612979600403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8370237234131483972800537 6277677925598612979600403)
          ·
            refine ⟨9416516888397919469400605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277677925598612979600403 9416516888397919469400605)
            ·
              refine ⟨3531193833149219801025227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9416516888397919469400605 3531193833149219801025227)
              ·
                refine ⟨5296790749723829701537841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531193833149219801025227 5296790749723829701537841)
                ·
                  refine ⟨3972593062292872276153381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5296790749723829701537841 3972593062292872276153381)
                  ·
                    refine ⟨744861199179913551778759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972593062292872276153381 744861199179913551778759)
                    ·
                      rfl

theorem cell23_4351836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_4351836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351836 prefixEnd_4351836 := by exact prefixLift 4351836
  have htrace : WordTrace (prefixWord ++ tailWord_4351836) baseStart_4351836 baseEnd_4351836 := by
    simpa [prefixWord, tailWord_4351836, baseEnd_4351836] using wordTrace_append hprefix tailTrace_4351836
  have hstable : (prefixWord ++ tailWord_4351836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351836).length < 2 ^ (prefixWord ++ tailWord_4351836).sum := by decide
  have hdescent : baseEnd_4351836 < baseStart_4351836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351903 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4351903 : Nat := 118140960795 + 4351903 * 2 ^ 59
def prefixEnd_4351903 : Nat := 4983230072969 + 3 ^ 40 * 4351903 * 2
def baseEnd_4351903 : Nat := 2234618000743591893198469

theorem tailTrace_4351903 : CollatzResearch.WordTrace tailWord_4351903 prefixEnd_4351903 2234618000743591893198469 := by
  unfold tailWord_4351903
  simp only [CollatzResearch.WordTrace]
  refine ⟨158726942352806151704684363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105817961568537434469789575 158726942352806151704684363)
  ·
    refine ⟨238090413529209227557026545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158726942352806151704684363 238090413529209227557026545)
    ·
      refine ⟨178567810146906920667769909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238090413529209227557026545 178567810146906920667769909)
      ·
        refine ⟨16740732201272523812603429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178567810146906920667769909 16740732201272523812603429)
        ·
          refine ⟨3138887287738598214863143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16740732201272523812603429 3138887287738598214863143)
          ·
            refine ⟨4708330931607897322294715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138887287738598214863143 4708330931607897322294715)
            ·
              refine ⟨7062496397411845983442073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708330931607897322294715 7062496397411845983442073)
              ·
                refine ⟨5296872298058884487581555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7062496397411845983442073 5296872298058884487581555)
                ·
                  refine ⟨7945308447088326731372333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5296872298058884487581555 7945308447088326731372333)
                  ·
                    refine ⟨2979490667658122524264625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945308447088326731372333 2979490667658122524264625)
                    ·
                      refine ⟨2234618000743591893198469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979490667658122524264625 2234618000743591893198469)
                      ·
                        rfl

theorem cell23_4351903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4351903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351903 prefixEnd_4351903 := by exact prefixLift 4351903
  have htrace : WordTrace (prefixWord ++ tailWord_4351903) baseStart_4351903 baseEnd_4351903 := by
    simpa [prefixWord, tailWord_4351903, baseEnd_4351903] using wordTrace_append hprefix tailTrace_4351903
  have hstable : (prefixWord ++ tailWord_4351903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351903).length < 2 ^ (prefixWord ++ tailWord_4351903).sum := by decide
  have hdescent : baseEnd_4351903 < baseStart_4351903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351935 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 2, 5]
def baseStart_4351935 : Nat := 118140960795 + 4351935 * 2 ^ 59
def prefixEnd_4351935 : Nat := 4983230072969 + 3 ^ 40 * 4351935 * 2
def baseEnd_4351935 : Nat := 744878144041511922666107

theorem tailTrace_4351935 : CollatzResearch.WordTrace tailWord_4351935 prefixEnd_4351935 744878144041511922666107 := by
  unfold tailWord_4351935
  simp only [CollatzResearch.WordTrace]
  refine ⟨158728109488690221169849259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105818739659126814113232839 158728109488690221169849259)
  ·
    refine ⟨238092164233035331754773889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158728109488690221169849259 238092164233035331754773889)
    ·
      refine ⟨178569123174776498816080417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238092164233035331754773889 178569123174776498816080417)
      ·
        refine ⟨133926842381082374112060313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178569123174776498816080417 133926842381082374112060313)
        ·
          refine ⟨100445131785811780584045235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133926842381082374112060313 100445131785811780584045235)
          ·
            refine ⟨150667697678717670876067853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100445131785811780584045235 150667697678717670876067853)
            ·
              refine ⟨56500386629519126578525445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150667697678717670876067853 56500386629519126578525445)
              ·
                refine ⟨10593822493034836233473521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56500386629519126578525445 10593822493034836233473521)
                ·
                  refine ⟨7945366869776127175105141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10593822493034836233473521 7945366869776127175105141)
                  ·
                    refine ⟨744878144041511922666107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7945366869776127175105141 744878144041511922666107)
                    ·
                      rfl

theorem cell23_4351935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_4351935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351935 prefixEnd_4351935 := by exact prefixLift 4351935
  have htrace : WordTrace (prefixWord ++ tailWord_4351935) baseStart_4351935 baseEnd_4351935 := by
    simpa [prefixWord, tailWord_4351935, baseEnd_4351935] using wordTrace_append hprefix tailTrace_4351935
  have hstable : (prefixWord ++ tailWord_4351935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351935).length < 2 ^ (prefixWord ++ tailWord_4351935).sum := by decide
  have hdescent : baseEnd_4351935 < baseStart_4351935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351972 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_4351972 : Nat := 118140960795 + 4351972 * 2 ^ 59
def prefixEnd_4351972 : Nat := 4983230072969 + 3 ^ 40 * 4351972 * 2
def baseEnd_4351972 : Nat := 2234653430908752123235651

theorem tailTrace_4351972 : CollatzResearch.WordTrace tailWord_4351972 prefixEnd_4351972 2234653430908752123235651 := by
  unfold tailWord_4351972
  simp only [CollatzResearch.WordTrace]
  refine ⟨79364729494778088244473085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105819639326370784325964113 79364729494778088244473085)
  ·
    refine ⟨29761773560541783091677407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79364729494778088244473085 29761773560541783091677407)
    ·
      refine ⟨44642660340812674637516111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29761773560541783091677407 44642660340812674637516111)
      ·
        refine ⟨66963990511219011956274167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44642660340812674637516111 66963990511219011956274167)
        ·
          refine ⟨100445985766828517934411251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66963990511219011956274167 100445985766828517934411251)
          ·
            refine ⟨150668978650242776901616877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100445985766828517934411251 150668978650242776901616877)
            ·
              refine ⟨56500866993841041338106329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150668978650242776901616877 56500866993841041338106329)
              ·
                refine ⟨42375650245380781003579747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56500866993841041338106329 42375650245380781003579747)
                ·
                  refine ⟨63563475368071171505369621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42375650245380781003579747 63563475368071171505369621)
                  ·
                    refine ⟨2979537907878336164314201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63563475368071171505369621 2979537907878336164314201)
                    ·
                      refine ⟨2234653430908752123235651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979537907878336164314201 2234653430908752123235651)
                      ·
                        rfl

theorem cell23_4351972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_4351972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351972 prefixEnd_4351972 := by exact prefixLift 4351972
  have htrace : WordTrace (prefixWord ++ tailWord_4351972) baseStart_4351972 baseEnd_4351972 := by
    simpa [prefixWord, tailWord_4351972, baseEnd_4351972] using wordTrace_append hprefix tailTrace_4351972
  have hstable : (prefixWord ++ tailWord_4351972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351972).length < 2 ^ (prefixWord ++ tailWord_4351972).sum := by decide
  have hdescent : baseEnd_4351972 < baseStart_4351972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4351992 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 2, 2, 3]
def baseStart_4351992 : Nat := 118140960795 + 4351992 * 2 ^ 59
def prefixEnd_4351992 : Nat := 4983230072969 + 3 ^ 40 * 4351992 * 2
def baseEnd_4351992 : Nat := 2234663700521842044985559

theorem tailTrace_4351992 : CollatzResearch.WordTrace tailWord_4351992 prefixEnd_4351992 2234663700521842044985559 := by
  unfold tailWord_4351992
  simp only [CollatzResearch.WordTrace]
  refine ⟨79365094224741859952337115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105820125632989146603116153 79365094224741859952337115)
  ·
    refine ⟨119047641337112789928505673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79365094224741859952337115 119047641337112789928505673)
    ·
      refine ⟨89285731002834592446379255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119047641337112789928505673 89285731002834592446379255)
      ·
        refine ⟨133928596504251888669568883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89285731002834592446379255 133928596504251888669568883)
        ·
          refine ⟨200892894756377833004353325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133928596504251888669568883 200892894756377833004353325)
          ·
            refine ⟨75334835533641687376632497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200892894756377833004353325 75334835533641687376632497)
            ·
              refine ⟨56501126650231265532474373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75334835533641687376632497 56501126650231265532474373)
              ·
                refine ⟨10593961246918362287338945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56501126650231265532474373 10593961246918362287338945)
                ·
                  refine ⟨7945470935188771715504209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10593961246918362287338945 7945470935188771715504209)
                  ·
                    refine ⟨5959103201391578786628157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7945470935188771715504209 5959103201391578786628157)
                    ·
                      refine ⟨2234663700521842044985559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959103201391578786628157 2234663700521842044985559)
                      ·
                        rfl

theorem cell23_4351992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_4351992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4351992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4351992 prefixEnd_4351992 := by exact prefixLift 4351992
  have htrace : WordTrace (prefixWord ++ tailWord_4351992) baseStart_4351992 baseEnd_4351992 := by
    simpa [prefixWord, tailWord_4351992, baseEnd_4351992] using wordTrace_append hprefix tailTrace_4351992
  have hstable : (prefixWord ++ tailWord_4351992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4351992).length < 2 ^ (prefixWord ++ tailWord_4351992).sum := by decide
  have hdescent : baseEnd_4351992 < baseStart_4351992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4351992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352033 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 1, 4]
def baseStart_4352033 : Nat := 118140960795 + 4352033 * 2 ^ 59
def prefixEnd_4352033 : Nat := 4983230072969 + 3 ^ 40 * 4352033 * 2
def baseEnd_4352033 : Nat := 744894917742892128190957

theorem tailTrace_4352033 : CollatzResearch.WordTrace tailWord_4352033 prefixEnd_4352033 744894917742892128190957 := by
  unfold tailWord_4352033
  simp only [CollatzResearch.WordTrace]
  refine ⟨158731683842335183906916753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105821122561556789271277835 158731683842335183906916753)
  ·
    refine ⟨119048762881751387930187565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158731683842335183906916753 119048762881751387930187565)
    ·
      refine ⟨44643286080656770473820337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119048762881751387930187565 44643286080656770473820337)
      ·
        refine ⟨33482464560492577855365253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44643286080656770473820337 33482464560492577855365253)
        ·
          refine ⟨6277962105092358347880985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33482464560492577855365253 6277962105092358347880985)
          ·
            refine ⟨4708471578819268760910739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6277962105092358347880985 4708471578819268760910739)
            ·
              refine ⟨7062707368228903141366109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708471578819268760910739 7062707368228903141366109)
              ·
                refine ⟨2648515263085838678012291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7062707368228903141366109 2648515263085838678012291)
                ·
                  refine ⟨3972772894628758017018437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648515263085838678012291 3972772894628758017018437)
                  ·
                    refine ⟨744894917742892128190957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972772894628758017018437 744894917742892128190957)
                    ·
                      rfl

theorem cell23_4352033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_4352033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352033 prefixEnd_4352033 := by exact prefixLift 4352033
  have htrace : WordTrace (prefixWord ++ tailWord_4352033) baseStart_4352033 baseEnd_4352033 := by
    simpa [prefixWord, tailWord_4352033, baseEnd_4352033] using wordTrace_append hprefix tailTrace_4352033
  have hstable : (prefixWord ++ tailWord_4352033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352033).length < 2 ^ (prefixWord ++ tailWord_4352033).sum := by decide
  have hdescent : baseEnd_4352033 < baseStart_4352033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352049 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 4, 3, 2]
def baseStart_4352049 : Nat := 118140960795 + 4352049 * 2 ^ 59
def prefixEnd_4352049 : Nat := 4983230072969 + 3 ^ 40 * 4352049 * 2
def baseEnd_4352049 : Nat := 2234692968919148321972797

theorem tailTrace_4352049 : CollatzResearch.WordTrace tailWord_4352049 prefixEnd_4352049 2234692968919148321972797 := by
  unfold tailWord_4352049
  simp only [CollatzResearch.WordTrace]
  refine ⟨158732267410277218639499201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105821511606851479092999467 158732267410277218639499201)
  ·
    refine ⟨119049200557707913979624401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158732267410277218639499201 119049200557707913979624401)
    ·
      refine ⟨89286900418280935484718301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119049200557707913979624401 89286900418280935484718301)
      ·
        refine ⟨33482587656855350806769363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89286900418280935484718301 33482587656855350806769363)
        ·
          refine ⟨50223881485283026210154045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33482587656855350806769363 50223881485283026210154045)
          ·
            refine ⟨18833955556981134828807767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50223881485283026210154045 18833955556981134828807767)
            ·
              refine ⟨28250933335471702243211651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18833955556981134828807767 28250933335471702243211651)
              ·
                refine ⟨42376400003207553364817477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28250933335471702243211651 42376400003207553364817477)
                ·
                  refine ⟨7945575000601416255903277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42376400003207553364817477 7945575000601416255903277)
                  ·
                    refine ⟨2979590625225531095963729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945575000601416255903277 2979590625225531095963729)
                    ·
                      refine ⟨2234692968919148321972797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979590625225531095963729 2234692968919148321972797)
                      ·
                        rfl

theorem cell23_4352049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_4352049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352049 prefixEnd_4352049 := by exact prefixLift 4352049
  have htrace : WordTrace (prefixWord ++ tailWord_4352049) baseStart_4352049 baseEnd_4352049 := by
    simpa [prefixWord, tailWord_4352049, baseEnd_4352049] using wordTrace_append hprefix tailTrace_4352049
  have hstable : (prefixWord ++ tailWord_4352049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352049).length < 2 ^ (prefixWord ++ tailWord_4352049).sum := by decide
  have hdescent : baseEnd_4352049 < baseStart_4352049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352072 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 6, 4]
def baseStart_4352072 : Nat := 118140960795 + 4352072 * 2 ^ 59
def prefixEnd_4352072 : Nat := 4983230072969 + 3 ^ 40 * 4352072 * 2
def baseEnd_4352072 : Nat := 744901592991400577328397

theorem tailTrace_4352072 : CollatzResearch.WordTrace tailWord_4352072 prefixEnd_4352072 744901592991400577328397 := by
  unfold tailWord_4352072
  simp only [CollatzResearch.WordTrace]
  refine ⟨79366553144596946783793235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105822070859462595711724313 79366553144596946783793235)
  ·
    refine ⟨119049829716895420175689853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79366553144596946783793235 119049829716895420175689853)
    ·
      refine ⟨44643686143835782565883695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119049829716895420175689853 44643686143835782565883695)
      ·
        refine ⟨66965529215753673848825543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44643686143835782565883695 66965529215753673848825543)
        ·
          refine ⟨100448293823630510773238315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66965529215753673848825543 100448293823630510773238315)
          ·
            refine ⟨150672440735445766159857473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100448293823630510773238315 150672440735445766159857473)
            ·
              refine ⟨113004330551584324619893105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150672440735445766159857473 113004330551584324619893105)
              ·
                refine ⟨84753247913688243464919829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113004330551584324619893105 84753247913688243464919829)
                ·
                  refine ⟨3972808495954136412418117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84753247913688243464919829 3972808495954136412418117)
                  ·
                    refine ⟨744901592991400577328397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972808495954136412418117 744901592991400577328397)
                    ·
                      rfl

theorem cell23_4352072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_4352072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352072 prefixEnd_4352072 := by exact prefixLift 4352072
  have htrace : WordTrace (prefixWord ++ tailWord_4352072) baseStart_4352072 baseEnd_4352072 := by
    simpa [prefixWord, tailWord_4352072, baseEnd_4352072] using wordTrace_append hprefix tailTrace_4352072
  have hstable : (prefixWord ++ tailWord_4352072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352072).length < 2 ^ (prefixWord ++ tailWord_4352072).sum := by decide
  have hdescent : baseEnd_4352072 < baseStart_4352072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352093 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4352093 : Nat := 118140960795 + 4352093 * 2 ^ 59
def prefixEnd_4352093 : Nat := 4983230072969 + 3 ^ 40 * 4352093 * 2
def baseEnd_4352093 : Nat := 744905187355982049940865

theorem tailTrace_4352093 : CollatzResearch.WordTrace tailWord_4352093 prefixEnd_4352093 744905187355982049940865 := by
  unfold tailWord_4352093
  simp only [CollatzResearch.WordTrace]
  refine ⟨158733872222117814154100933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105822581481411876102733955 158733872222117814154100933)
  ·
    refine ⟨29762601041647090153893925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158733872222117814154100933 29762601041647090153893925)
    ·
      refine ⟨5580487695308829403855111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29762601041647090153893925 5580487695308829403855111)
      ·
        refine ⟨8370731542963244105782667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5580487695308829403855111 8370731542963244105782667)
        ·
          refine ⟨12556097314444866158674001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8370731542963244105782667 12556097314444866158674001)
          ·
            refine ⟨9417072985833649619005501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12556097314444866158674001 9417072985833649619005501)
            ·
              refine ⟨3531402369687618607127063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9417072985833649619005501 3531402369687618607127063)
              ·
                refine ⟨5297103554531427910690595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531402369687618607127063 5297103554531427910690595)
                ·
                  refine ⟨7945655331797141866035893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297103554531427910690595 7945655331797141866035893)
                  ·
                    refine ⟨744905187355982049940865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7945655331797141866035893 744905187355982049940865)
                    ·
                      rfl

theorem cell23_4352093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4352093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352093 prefixEnd_4352093 := by exact prefixLift 4352093
  have htrace : WordTrace (prefixWord ++ tailWord_4352093) baseStart_4352093 baseEnd_4352093 := by
    simpa [prefixWord, tailWord_4352093, baseEnd_4352093] using wordTrace_append hprefix tailTrace_4352093
  have hstable : (prefixWord ++ tailWord_4352093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352093).length < 2 ^ (prefixWord ++ tailWord_4352093).sum := by decide
  have hdescent : baseEnd_4352093 < baseStart_4352093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352096 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 1, 1, 4]
def baseStart_4352096 : Nat := 118140960795 + 4352096 * 2 ^ 59
def prefixEnd_4352096 : Nat := 4983230072969 + 3 ^ 40 * 4352096 * 2
def baseEnd_4352096 : Nat := 2234717102509909638085081

theorem tailTrace_4352096 : CollatzResearch.WordTrace tailWord_4352096 prefixEnd_4352096 2234717102509909638085081 := by
  unfold tailWord_4352096
  simp only [CollatzResearch.WordTrace]
  refine ⟨79366990820553472833230071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105822654427404630444306761 79366990820553472833230071)
  ·
    refine ⟨119050486230830209249845107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79366990820553472833230071 119050486230830209249845107)
    ·
      refine ⟨178575729346245313874767661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119050486230830209249845107 178575729346245313874767661)
      ·
        refine ⟨66965898504841992703037873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178575729346245313874767661 66965898504841992703037873)
        ·
          refine ⟨50224423878631494527278405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66965898504841992703037873 50224423878631494527278405)
          ·
            refine ⟨9417079477243405223864701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50224423878631494527278405 9417079477243405223864701)
            ·
              refine ⟨3531404803966276958949263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9417079477243405223864701 3531404803966276958949263)
              ·
                refine ⟨5297107205949415438423895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531404803966276958949263 5297107205949415438423895)
                ·
                  refine ⟨7945660808924123157635843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297107205949415438423895 7945660808924123157635843)
                  ·
                    refine ⟨11918491213386184736453765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7945660808924123157635843 11918491213386184736453765)
                    ·
                      refine ⟨2234717102509909638085081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11918491213386184736453765 2234717102509909638085081)
                      ·
                        rfl

theorem cell23_4352096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_4352096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352096 prefixEnd_4352096 := by exact prefixLift 4352096
  have htrace : WordTrace (prefixWord ++ tailWord_4352096) baseStart_4352096 baseEnd_4352096 := by
    simpa [prefixWord, tailWord_4352096, baseEnd_4352096] using wordTrace_append hprefix tailTrace_4352096
  have hstable : (prefixWord ++ tailWord_4352096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352096).length < 2 ^ (prefixWord ++ tailWord_4352096).sum := by decide
  have hdescent : baseEnd_4352096 < baseStart_4352096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352099 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 3]
def baseStart_4352099 : Nat := 118140960795 + 4352099 * 2 ^ 59
def prefixEnd_4352099 : Nat := 4983230072969 + 3 ^ 40 * 4352099 * 2
def baseEnd_4352099 : Nat := 2234718642951873126347567

theorem tailTrace_4352099 : CollatzResearch.WordTrace tailWord_4352099 prefixEnd_4352099 2234718642951873126347567 := by
  unfold tailWord_4352099
  simp only [CollatzResearch.WordTrace]
  refine ⟨158734091060096077178819351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105822727373397384785879567 158734091060096077178819351)
  ·
    refine ⟨238101136590144115768229027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158734091060096077178819351 238101136590144115768229027)
    ·
      refine ⟨357151704885216173652343541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238101136590144115768229027 357151704885216173652343541)
      ·
        refine ⟨33482972332989016279907207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 357151704885216173652343541 33482972332989016279907207)
        ·
          refine ⟨50224458499483524419860811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33482972332989016279907207 50224458499483524419860811)
          ·
            refine ⟨75336687749225286629791217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50224458499483524419860811 75336687749225286629791217)
            ·
              refine ⟨56502515811918964972343413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75336687749225286629791217 56502515811918964972343413)
              ·
                refine ⟨5297110857367402966157195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56502515811918964972343413 5297110857367402966157195)
                ·
                  refine ⟨7945666286051104449235793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297110857367402966157195 7945666286051104449235793)
                  ·
                    refine ⟨5959249714538328336926845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7945666286051104449235793 5959249714538328336926845)
                    ·
                      refine ⟨2234718642951873126347567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959249714538328336926845 2234718642951873126347567)
                      ·
                        rfl

theorem cell23_4352099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_4352099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352099 prefixEnd_4352099 := by exact prefixLift 4352099
  have htrace : WordTrace (prefixWord ++ tailWord_4352099) baseStart_4352099 baseEnd_4352099 := by
    simpa [prefixWord, tailWord_4352099, baseEnd_4352099] using wordTrace_append hprefix tailTrace_4352099
  have hstable : (prefixWord ++ tailWord_4352099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352099).length < 2 ^ (prefixWord ++ tailWord_4352099).sum := by decide
  have hdescent : baseEnd_4352099 < baseStart_4352099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352113 : List Nat := [1, 2, 2, 2, 1, 1, 5, 4, 1, 2, 2]
def baseStart_4352113 : Nat := 118140960795 + 4352113 * 2 ^ 59
def prefixEnd_4352113 : Nat := 4983230072969 + 3 ^ 40 * 4352113 * 2
def baseEnd_4352113 : Nat := 2234725831681036071572503

theorem tailTrace_4352113 : CollatzResearch.WordTrace tailWord_4352113 prefixEnd_4352113 2234725831681036071572503 := by
  unfold tailWord_4352113
  simp only [CollatzResearch.WordTrace]
  refine ⟨158734601682045357569828993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105823067788030238379885995 158734601682045357569828993)
  ·
    refine ⟨119050951261534018177371745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158734601682045357569828993 119050951261534018177371745)
    ·
      refine ⟨89288213446150513633028809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119050951261534018177371745 89288213446150513633028809)
      ·
        refine ⟨66966160084612885224771607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89288213446150513633028809 66966160084612885224771607)
        ·
          refine ⟨100449240126919327837157411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66966160084612885224771607 100449240126919327837157411)
          ·
            refine ⟨150673860190378991755736117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100449240126919327837157411 150673860190378991755736117)
            ·
              refine ⟨14125674392848030477100261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150673860190378991755736117 14125674392848030477100261)
              ·
                refine ⟨2648563948659005714456299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14125674392848030477100261 2648563948659005714456299)
                ·
                  refine ⟨3972845922988508571684449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648563948659005714456299 3972845922988508571684449)
                  ·
                    refine ⟨2979634442241381428763337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3972845922988508571684449 2979634442241381428763337)
                    ·
                      refine ⟨2234725831681036071572503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979634442241381428763337 2234725831681036071572503)
                      ·
                        rfl

theorem cell23_4352113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_4352113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352113 prefixEnd_4352113 := by exact prefixLift 4352113
  have htrace : WordTrace (prefixWord ++ tailWord_4352113) baseStart_4352113 baseEnd_4352113 := by
    simpa [prefixWord, tailWord_4352113, baseEnd_4352113] using wordTrace_append hprefix tailTrace_4352113
  have hstable : (prefixWord ++ tailWord_4352113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352113).length < 2 ^ (prefixWord ++ tailWord_4352113).sum := by decide
  have hdescent : baseEnd_4352113 < baseStart_4352113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352132 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_4352132 : Nat := 118140960795 + 4352132 * 2 ^ 59
def prefixEnd_4352132 : Nat := 4983230072969 + 3 ^ 40 * 4352132 * 2
def baseEnd_4352132 : Nat := 744911862604490499078305

theorem tailTrace_4352132 : CollatzResearch.WordTrace tailWord_4352132 prefixEnd_4352132 744911862604490499078305 := by
  unfold tailWord_4352132
  simp only [CollatzResearch.WordTrace]
  refine ⟨79367647334488261907385325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105823529779317682543180433 79367647334488261907385325)
  ·
    refine ⟨29762867750433098215269497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79367647334488261907385325 29762867750433098215269497)
    ·
      refine ⟨22322150812824823661452123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29762867750433098215269497 22322150812824823661452123)
      ·
        refine ⟨33483226219237235492178185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22322150812824823661452123 33483226219237235492178185)
        ·
          refine ⟨25112419664427926619133639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33483226219237235492178185 25112419664427926619133639)
          ·
            refine ⟨37668629496641889928700459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25112419664427926619133639 37668629496641889928700459)
            ·
              refine ⟨56502944244962834893050689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37668629496641889928700459 56502944244962834893050689)
              ·
                refine ⟨42377208183722126169788017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56502944244962834893050689 42377208183722126169788017)
                ·
                  refine ⟨31782906137791594627341013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42377208183722126169788017 31782906137791594627341013)
                  ·
                    refine ⟨744911862604490499078305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31782906137791594627341013 744911862604490499078305)
                    ·
                      rfl

theorem cell23_4352132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_4352132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352132 prefixEnd_4352132 := by exact prefixLift 4352132
  have htrace : WordTrace (prefixWord ++ tailWord_4352132) baseStart_4352132 baseEnd_4352132 := by
    simpa [prefixWord, tailWord_4352132, baseEnd_4352132] using wordTrace_append hprefix tailTrace_4352132
  have hstable : (prefixWord ++ tailWord_4352132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352132).length < 2 ^ (prefixWord ++ tailWord_4352132).sum := by decide
  have hdescent : baseEnd_4352132 < baseStart_4352132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352146 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_4352146 : Nat := 118140960795 + 4352146 * 2 ^ 59
def prefixEnd_4352146 : Nat := 4983230072969 + 3 ^ 40 * 4352146 * 2
def baseEnd_4352146 : Nat := 2234742776542634442459851

theorem tailTrace_4352146 : CollatzResearch.WordTrace tailWord_4352146 prefixEnd_4352146 2234742776542634442459851 := by
  unfold tailWord_4352146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39683951322731451051445073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105823870193950536137186861 39683951322731451051445073)
  ·
    refine ⟨29762963492048588288583805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39683951322731451051445073 29762963492048588288583805)
    ·
      refine ⟨11161111309518220608218927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29762963492048588288583805 11161111309518220608218927)
      ·
        refine ⟨16741666964277330912328391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11161111309518220608218927 16741666964277330912328391)
        ·
          refine ⟨25112500446415996368492587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16741666964277330912328391 25112500446415996368492587)
          ·
            refine ⟨37668750669623994552738881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25112500446415996368492587 37668750669623994552738881)
            ·
              refine ⟨28251563002217995914554161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37668750669623994552738881 28251563002217995914554161)
              ·
                refine ⟨21188672251663496935915621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28251563002217995914554161 21188672251663496935915621)
                ·
                  refine ⟨3972876047186905675484179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21188672251663496935915621 3972876047186905675484179)
                  ·
                    refine ⟨5959314070780358513226269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3972876047186905675484179 5959314070780358513226269)
                    ·
                      refine ⟨2234742776542634442459851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959314070780358513226269 2234742776542634442459851)
                      ·
                        rfl

theorem cell23_4352146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_4352146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352146 prefixEnd_4352146 := by exact prefixLift 4352146
  have htrace : WordTrace (prefixWord ++ tailWord_4352146) baseStart_4352146 baseEnd_4352146 := by
    simpa [prefixWord, tailWord_4352146, baseEnd_4352146] using wordTrace_append hprefix tailTrace_4352146
  have hstable : (prefixWord ++ tailWord_4352146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352146).length < 2 ^ (prefixWord ++ tailWord_4352146).sum := by decide
  have hdescent : baseEnd_4352146 < baseStart_4352146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352186 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2]
def baseStart_4352186 : Nat := 118140960795 + 4352186 * 2 ^ 59
def prefixEnd_4352186 : Nat := 4983230072969 + 3 ^ 40 * 4352186 * 2
def baseEnd_4352186 : Nat := 2234763315768814285959667

theorem tailTrace_4352186 : CollatzResearch.WordTrace tailWord_4352186 prefixEnd_4352186 2234763315768814285959667 := by
  unfold tailWord_4352186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39684316052695222759309103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105824842807187260691490941 39684316052695222759309103)
  ·
    refine ⟨59526474079042834138963655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39684316052695222759309103 59526474079042834138963655)
    ·
      refine ⟨89289711118564251208445483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59526474079042834138963655 89289711118564251208445483)
      ·
        refine ⟨133934566677846376812668225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89289711118564251208445483 133934566677846376812668225)
        ·
          refine ⟨100450925008384782609501169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133934566677846376812668225 100450925008384782609501169)
          ·
            refine ⟨75338193756288586957125877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100450925008384782609501169 75338193756288586957125877)
            ·
              refine ⟨7062955664652055027230551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75338193756288586957125877 7062955664652055027230551)
              ·
                refine ⟨10594433496978082540845827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7062955664652055027230551 10594433496978082540845827)
                ·
                  refine ⟨15891650245467123811268741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10594433496978082540845827 15891650245467123811268741)
                  ·
                    refine ⟨2979684421025085714612889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15891650245467123811268741 2979684421025085714612889)
                    ·
                      refine ⟨2234763315768814285959667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979684421025085714612889 2234763315768814285959667)
                      ·
                        rfl

theorem cell23_4352186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_4352186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352186 prefixEnd_4352186 := by exact prefixLift 4352186
  have htrace : WordTrace (prefixWord ++ tailWord_4352186) baseStart_4352186 baseEnd_4352186 := by
    simpa [prefixWord, tailWord_4352186, baseEnd_4352186] using wordTrace_append hprefix tailTrace_4352186
  have hstable : (prefixWord ++ tailWord_4352186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352186).length < 2 ^ (prefixWord ++ tailWord_4352186).sum := by decide
  have hdescent : baseEnd_4352186 < baseStart_4352186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352190 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_4352190 : Nat := 118140960795 + 4352190 * 2 ^ 59
def prefixEnd_4352190 : Nat := 4983230072969 + 3 ^ 40 * 4352190 * 2
def baseEnd_4352190 : Nat := 2234765369691432270309649

theorem tailTrace_4352190 : CollatzResearch.WordTrace tailWord_4352190 prefixEnd_4352190 2234765369691432270309649 := by
  unfold tailWord_4352190
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842176262845799965047753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105824940068510933146921349 19842176262845799965047753)
  ·
    refine ⟨14881632197134349973785815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19842176262845799965047753 14881632197134349973785815)
    ·
      refine ⟨22322448295701524960678723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14881632197134349973785815 22322448295701524960678723)
      ·
        refine ⟨33483672443552287441018085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22322448295701524960678723 33483672443552287441018085)
        ·
          refine ⟨6278188583166053895190891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33483672443552287441018085 6278188583166053895190891)
          ·
            refine ⟨9417282874749080842786337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6278188583166053895190891 9417282874749080842786337)
            ·
              refine ⟨7062962156061810632089753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9417282874749080842786337 7062962156061810632089753)
              ·
                refine ⟨5297221617046357974067315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7062962156061810632089753 5297221617046357974067315)
                ·
                  refine ⟨7945832425569536961100973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297221617046357974067315 7945832425569536961100973)
                  ·
                    refine ⟨2979687159588576360412865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945832425569536961100973 2979687159588576360412865)
                    ·
                      refine ⟨2234765369691432270309649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979687159588576360412865 2234765369691432270309649)
                      ·
                        rfl

theorem cell23_4352190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_4352190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352190 prefixEnd_4352190 := by exact prefixLift 4352190
  have htrace : WordTrace (prefixWord ++ tailWord_4352190) baseStart_4352190 baseEnd_4352190 := by
    simpa [prefixWord, tailWord_4352190, baseEnd_4352190] using wordTrace_append hprefix tailTrace_4352190
  have hstable : (prefixWord ++ tailWord_4352190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352190).length < 2 ^ (prefixWord ++ tailWord_4352190).sum := by decide
  have hdescent : baseEnd_4352190 < baseStart_4352190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352293 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 2, 4, 2]
def baseStart_4352293 : Nat := 118140960795 + 4352293 * 2 ^ 59
def prefixEnd_4352293 : Nat := 4983230072969 + 3 ^ 40 * 4352293 * 2
def baseEnd_4352293 : Nat := 2234818258198845367321675

theorem tailTrace_4352293 : CollatzResearch.WordTrace tailWord_4352293 prefixEnd_4352293 2234818258198845367321675 := by
  unfold tailWord_4352293
  simp only [CollatzResearch.WordTrace]
  refine ⟨158741166821393248311381533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105827444547595498874254355 158741166821393248311381533)
  ·
    refine ⟨59527937558022468116768075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158741166821393248311381533 59527937558022468116768075)
    ·
      refine ⟨89291906337033702175152113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59527937558022468116768075 89291906337033702175152113)
      ·
        refine ⟨66968929752775276631364085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89291906337033702175152113 66968929752775276631364085)
        ·
          refine ⟨6278337164322682184190383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66968929752775276631364085 6278337164322682184190383)
          ·
            refine ⟨9417505746484023276285575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6278337164322682184190383 9417505746484023276285575)
            ·
              refine ⟨14126258619726034914428363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9417505746484023276285575 14126258619726034914428363)
              ·
                refine ⟨21189387929589052371642545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14126258619726034914428363 21189387929589052371642545)
                ·
                  refine ⟨15892040947191789278731909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21189387929589052371642545 15892040947191789278731909)
                  ·
                    refine ⟨2979757677598460489762233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15892040947191789278731909 2979757677598460489762233)
                    ·
                      refine ⟨2234818258198845367321675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2979757677598460489762233 2234818258198845367321675)
                      ·
                        rfl

theorem cell23_4352293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_4352293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352293 prefixEnd_4352293 := by exact prefixLift 4352293
  have htrace : WordTrace (prefixWord ++ tailWord_4352293) baseStart_4352293 baseEnd_4352293 := by
    simpa [prefixWord, tailWord_4352293, baseEnd_4352293] using wordTrace_append hprefix tailTrace_4352293
  have hstable : (prefixWord ++ tailWord_4352293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352293).length < 2 ^ (prefixWord ++ tailWord_4352293).sum := by decide
  have hdescent : baseEnd_4352293 < baseStart_4352293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4352313 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_4352313 : Nat := 118140960795 + 4352313 * 2 ^ 59
def prefixEnd_4352313 : Nat := 4983230072969 + 3 ^ 40 * 4352313 * 2
def baseEnd_4352313 : Nat := 2234828527811935289071583

theorem tailTrace_4352313 : CollatzResearch.WordTrace tailWord_4352313 prefixEnd_4352313 2234828527811935289071583 := by
  unfold tailWord_4352313
  simp only [CollatzResearch.WordTrace]
  refine ⟨158741896281320791727109593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105827930854213861151406395 158741896281320791727109593)
  ·
    refine ⟨119056422210990593795332195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158741896281320791727109593 119056422210990593795332195)
    ·
      refine ⟨178584633316485890692998293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119056422210990593795332195 178584633316485890692998293)
      ·
        refine ⟨8371154686710276126234295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 178584633316485890692998293 8371154686710276126234295)
        ·
          refine ⟨12556732030065414189351443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8371154686710276126234295 12556732030065414189351443)
          ·
            refine ⟨18835098045098121284027165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12556732030065414189351443 18835098045098121284027165)
            ·
              refine ⟨7063161766911795481510187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18835098045098121284027165 7063161766911795481510187)
              ·
                refine ⟨10594742650367693222265281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7063161766911795481510187 10594742650367693222265281)
                ·
                  refine ⟨7946056987775769916698961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10594742650367693222265281 7946056987775769916698961)
                  ·
                    refine ⟨5959542740831827437524221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7946056987775769916698961 5959542740831827437524221)
                    ·
                      refine ⟨2234828527811935289071583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5959542740831827437524221 2234828527811935289071583)
                      ·
                        rfl

theorem cell23_4352313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_4352313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4352313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4352313 prefixEnd_4352313 := by exact prefixLift 4352313
  have htrace : WordTrace (prefixWord ++ tailWord_4352313) baseStart_4352313 baseEnd_4352313 := by
    simpa [prefixWord, tailWord_4352313, baseEnd_4352313] using wordTrace_append hprefix tailTrace_4352313
  have hstable : (prefixWord ++ tailWord_4352313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4352313).length < 2 ^ (prefixWord ++ tailWord_4352313).sum := by decide
  have hdescent : baseEnd_4352313 < baseStart_4352313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4352313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
