import V185TrunkScan23Chunk0876

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5189832 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_5189832 : Nat := 118140960795 + 5189832 * 2 ^ 59
def prefixEnd_5189832 : Nat := 4983230072969 + 3 ^ 40 * 5189832 * 2
def baseEnd_5189832 : Nat := 2664878332084843992132403

theorem tailTrace_5189832 : CollatzResearch.WordTrace tailWord_5189832 prefixEnd_5189832 2664878332084843992132403 := by
  unfold tailWord_5189832
  simp only [CollatzResearch.WordTrace]
  refine ⟨94644361867066245792281875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126192482489421661056375833 94644361867066245792281875)
  ·
    refine ⟨141966542800599368688422813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94644361867066245792281875 141966542800599368688422813)
    ·
      refine ⟨53237453550224763258158555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141966542800599368688422813 53237453550224763258158555)
      ·
        refine ⟨79856180325337144887237833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53237453550224763258158555 79856180325337144887237833)
        ·
          refine ⟨59892135244002858665428375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79856180325337144887237833 59892135244002858665428375)
          ·
            refine ⟨89838202866004287998142563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59892135244002858665428375 89838202866004287998142563)
            ·
              refine ⟨134757304299006431997213845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89838202866004287998142563 134757304299006431997213845)
              ·
                refine ⟨6316748639015926499869399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134757304299006431997213845 6316748639015926499869399)
                ·
                  refine ⟨9475122958523889749804099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316748639015926499869399 9475122958523889749804099)
                  ·
                    refine ⟨14212684437785834624706149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9475122958523889749804099 14212684437785834624706149)
                    ·
                      refine ⟨2664878332084843992132403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14212684437785834624706149 2664878332084843992132403)
                      ·
                        rfl

theorem cell23_5189832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_5189832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189832 prefixEnd_5189832 := by exact prefixLift 5189832
  have htrace : WordTrace (prefixWord ++ tailWord_5189832) baseStart_5189832 baseEnd_5189832 := by
    simpa [prefixWord, tailWord_5189832, baseEnd_5189832] using wordTrace_append hprefix tailTrace_5189832
  have hstable : (prefixWord ++ tailWord_5189832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189832).length < 2 ^ (prefixWord ++ tailWord_5189832).sum := by decide
  have hdescent : baseEnd_5189832 < baseStart_5189832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189836 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5189836 : Nat := 118140960795 + 5189836 * 2 ^ 59
def prefixEnd_5189836 : Nat := 4983230072969 + 3 ^ 40 * 5189836 * 2
def baseEnd_5189836 : Nat := 2664880386007461976482385

theorem tailTrace_5189836 : CollatzResearch.WordTrace tailWord_5189836 prefixEnd_5189836 2664880386007461976482385 := by
  unfold tailWord_5189836
  simp only [CollatzResearch.WordTrace]
  refine ⟨94644434813059000133854681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126192579750745333511806241 94644434813059000133854681)
  ·
    refine ⟨70983326109794250100391011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94644434813059000133854681 70983326109794250100391011)
    ·
      refine ⟨106474989164691375150586517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70983326109794250100391011 106474989164691375150586517)
      ·
        refine ⟨4991015117094908210183743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106474989164691375150586517 4991015117094908210183743)
        ·
          refine ⟨7486522675642362315275615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991015117094908210183743 7486522675642362315275615)
          ·
            refine ⟨11229784013463543472913423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7486522675642362315275615 11229784013463543472913423)
            ·
              refine ⟨16844676020195315209370135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11229784013463543472913423 16844676020195315209370135)
              ·
                refine ⟨25267014030292972814055203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16844676020195315209370135 25267014030292972814055203)
                ·
                  refine ⟨37900521045439459221082805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25267014030292972814055203 37900521045439459221082805)
                  ·
                    refine ⟨3553173848009949301976513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37900521045439459221082805 3553173848009949301976513)
                    ·
                      refine ⟨2664880386007461976482385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553173848009949301976513 2664880386007461976482385)
                      ·
                        rfl

theorem cell23_5189836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5189836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189836 prefixEnd_5189836 := by exact prefixLift 5189836
  have htrace : WordTrace (prefixWord ++ tailWord_5189836) baseStart_5189836 baseEnd_5189836 := by
    simpa [prefixWord, tailWord_5189836, baseEnd_5189836] using wordTrace_append hprefix tailTrace_5189836
  have hstable : (prefixWord ++ tailWord_5189836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189836).length < 2 ^ (prefixWord ++ tailWord_5189836).sum := by decide
  have hdescent : baseEnd_5189836 < baseStart_5189836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189842 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_5189842 : Nat := 118140960795 + 5189842 * 2 ^ 59
def prefixEnd_5189842 : Nat := 4983230072969 + 3 ^ 40 * 5189842 * 2
def baseEnd_5189842 : Nat := 888294488963796317669119

theorem tailTrace_5189842 : CollatzResearch.WordTrace tailWord_5189842 prefixEnd_5189842 888294488963796317669119 := by
  unfold tailWord_5189842
  simp only [CollatzResearch.WordTrace]
  refine ⟨47322272116024065823106945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126192725642730842194951853 47322272116024065823106945)
  ·
    refine ⟨35491704087018049367330209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47322272116024065823106945 35491704087018049367330209)
    ·
      refine ⟨26618778065263537025497657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35491704087018049367330209 26618778065263537025497657)
      ·
        refine ⟨19964083548947652769123243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26618778065263537025497657 19964083548947652769123243)
        ·
          refine ⟨29946125323421479153684865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19964083548947652769123243 29946125323421479153684865)
          ·
            refine ⟨22459593992566109365263649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29946125323421479153684865 22459593992566109365263649)
            ·
              refine ⟨16844695494424582023947737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22459593992566109365263649 16844695494424582023947737)
              ·
                refine ⟨12633521620818436517960803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16844695494424582023947737 12633521620818436517960803)
                ·
                  refine ⟨18950282431227654776941205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12633521620818436517960803 18950282431227654776941205)
                  ·
                    refine ⟨888294488963796317669119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18950282431227654776941205 888294488963796317669119)
                    ·
                      rfl

theorem cell23_5189842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_5189842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189842 prefixEnd_5189842 := by exact prefixLift 5189842
  have htrace : WordTrace (prefixWord ++ tailWord_5189842) baseStart_5189842 baseEnd_5189842 := by
    simpa [prefixWord, tailWord_5189842, baseEnd_5189842] using wordTrace_append hprefix tailTrace_5189842
  have hstable : (prefixWord ++ tailWord_5189842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189842).length < 2 ^ (prefixWord ++ tailWord_5189842).sum := by decide
  have hdescent : baseEnd_5189842 < baseStart_5189842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189846 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_5189846 : Nat := 118140960795 + 5189846 * 2 ^ 59
def prefixEnd_5189846 : Nat := 4983230072969 + 3 ^ 40 * 5189846 * 2
def baseEnd_5189846 : Nat := 888295173604668979119113

theorem tailTrace_5189846 : CollatzResearch.WordTrace tailWord_5189846 prefixEnd_5189846 888295173604668979119113 := by
  unfold tailWord_5189846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830577147255110748473337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126192822904054514650382261 11830577147255110748473337)
  ·
    refine ⟨8872932860441333061355003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11830577147255110748473337 8872932860441333061355003)
    ·
      refine ⟨13309399290661999592032505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8872932860441333061355003 13309399290661999592032505)
      ·
        refine ⟨9982049467996499694024379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13309399290661999592032505 9982049467996499694024379)
        ·
          refine ⟨14973074201994749541036569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982049467996499694024379 14973074201994749541036569)
          ·
            refine ⟨11229805651496062155777427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14973074201994749541036569 11229805651496062155777427)
            ·
              refine ⟨16844708477244093233666141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11229805651496062155777427 16844708477244093233666141)
              ·
                refine ⟨6316765678966534962624803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16844708477244093233666141 6316765678966534962624803)
                ·
                  refine ⟨9475148518449802443937205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316765678966534962624803 9475148518449802443937205)
                  ·
                    refine ⟨888295173604668979119113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9475148518449802443937205 888295173604668979119113)
                    ·
                      rfl

theorem cell23_5189846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_5189846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189846 prefixEnd_5189846 := by exact prefixLift 5189846
  have htrace : WordTrace (prefixWord ++ tailWord_5189846) baseStart_5189846 baseEnd_5189846 := by
    simpa [prefixWord, tailWord_5189846, baseEnd_5189846] using wordTrace_append hprefix tailTrace_5189846
  have hstable : (prefixWord ++ tailWord_5189846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189846).length < 2 ^ (prefixWord ++ tailWord_5189846).sum := by decide
  have hdescent : baseEnd_5189846 < baseStart_5189846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189849 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 1, 1, 4]
def baseStart_5189849 : Nat := 118140960795 + 5189849 * 2 ^ 59
def prefixEnd_5189849 : Nat := 4983230072969 + 3 ^ 40 * 5189849 * 2
def baseEnd_5189849 : Nat := 2664887061255970425619825

theorem tailTrace_5189849 : CollatzResearch.WordTrace tailWord_5189849 prefixEnd_5189849 2664887061255970425619825 := by
  unfold tailWord_5189849
  simp only [CollatzResearch.WordTrace]
  refine ⟨189289343775070903487932601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126192895850047268991955067 189289343775070903487932601)
  ·
    refine ⟨141967007831303177615949451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189289343775070903487932601 141967007831303177615949451)
    ·
      refine ⟨212950511746954766423924177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141967007831303177615949451 212950511746954766423924177)
      ·
        refine ⟨159712883810216074817943133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212950511746954766423924177 159712883810216074817943133)
        ·
          refine ⟨59892331428831028056728675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159712883810216074817943133 59892331428831028056728675)
          ·
            refine ⟨89838497143246542085093013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59892331428831028056728675 89838497143246542085093013)
            ·
              refine ⟨4211179553589681660238735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89838497143246542085093013 4211179553589681660238735)
              ·
                refine ⟨6316769330384522490358103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211179553589681660238735 6316769330384522490358103)
                ·
                  refine ⟨9475153995576783735537155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316769330384522490358103 9475153995576783735537155)
                  ·
                    refine ⟨14212730993365175603305733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9475153995576783735537155 14212730993365175603305733)
                    ·
                      refine ⟨2664887061255970425619825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14212730993365175603305733 2664887061255970425619825)
                      ·
                        rfl

theorem cell23_5189849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_5189849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189849 prefixEnd_5189849 := by exact prefixLift 5189849
  have htrace : WordTrace (prefixWord ++ tailWord_5189849) baseStart_5189849 baseEnd_5189849 := by
    simpa [prefixWord, tailWord_5189849, baseEnd_5189849] using wordTrace_append hprefix tailTrace_5189849
  have hstable : (prefixWord ++ tailWord_5189849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189849).length < 2 ^ (prefixWord ++ tailWord_5189849).sum := by decide
  have hdescent : baseEnd_5189849 < baseStart_5189849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189866 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_5189866 : Nat := 118140960795 + 5189866 * 2 ^ 59
def prefixEnd_5189866 : Nat := 4983230072969 + 3 ^ 40 * 5189866 * 2
def baseEnd_5189866 : Nat := 2664895790427096859107247

theorem tailTrace_5189866 : CollatzResearch.WordTrace tailWord_5189866 prefixEnd_5189866 2664895790427096859107247 := by
  unfold tailWord_5189866
  simp only [CollatzResearch.WordTrace]
  refine ⟨47322490954002328847825363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126193309210672876927534301 47322490954002328847825363)
  ·
    refine ⟨70983736431003493271738045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47322490954002328847825363 70983736431003493271738045)
    ·
      refine ⟨26618901161626309976901767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70983736431003493271738045 26618901161626309976901767)
      ·
        refine ⟨39928351742439464965352651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26618901161626309976901767 39928351742439464965352651)
        ·
          refine ⟨59892527613659197448028977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39928351742439464965352651 59892527613659197448028977)
          ·
            refine ⟨44919395710244398086021733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59892527613659197448028977 44919395710244398086021733)
            ·
              refine ⟨8422386695670824641129075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44919395710244398086021733 8422386695670824641129075)
              ·
                refine ⟨12633580043506236961693613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8422386695670824641129075 12633580043506236961693613)
                ·
                  refine ⟨4737592516314838860635105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12633580043506236961693613 4737592516314838860635105)
                  ·
                    refine ⟨3553194387236129145476329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737592516314838860635105 3553194387236129145476329)
                    ·
                      refine ⟨2664895790427096859107247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553194387236129145476329 2664895790427096859107247)
                      ·
                        rfl

theorem cell23_5189866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_5189866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189866 prefixEnd_5189866 := by exact prefixLift 5189866
  have htrace : WordTrace (prefixWord ++ tailWord_5189866) baseStart_5189866 baseEnd_5189866 := by
    simpa [prefixWord, tailWord_5189866, baseEnd_5189866] using wordTrace_append hprefix tailTrace_5189866
  have hstable : (prefixWord ++ tailWord_5189866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189866).length < 2 ^ (prefixWord ++ tailWord_5189866).sum := by decide
  have hdescent : baseEnd_5189866 < baseStart_5189866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189869 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5189869 : Nat := 118140960795 + 5189869 * 2 ^ 59
def prefixEnd_5189869 : Nat := 4983230072969 + 3 ^ 40 * 5189869 * 2
def baseEnd_5189869 : Nat := 2664897330869060347369733

theorem tailTrace_5189869 : CollatzResearch.WordTrace tailWord_5189869 prefixEnd_5189869 2664897330869060347369733 := by
  unfold tailWord_5189869
  simp only [CollatzResearch.WordTrace]
  refine ⟨189290073234998446903660661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126193382156665631269107107 189290073234998446903660661)
  ·
    refine ⟨17745944365781104397218187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189290073234998446903660661 17745944365781104397218187)
    ·
      refine ⟨26618916548671656595827281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17745944365781104397218187 26618916548671656595827281)
      ·
        refine ⟨19964187411503742446870461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26618916548671656595827281 19964187411503742446870461)
        ·
          refine ⟨7486570279313903417576423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19964187411503742446870461 7486570279313903417576423)
          ·
            refine ⟨11229855418970855126364635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7486570279313903417576423 11229855418970855126364635)
            ·
              refine ⟨16844783128456282689546953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11229855418970855126364635 16844783128456282689546953)
              ·
                refine ⟨12633587346342212017160215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16844783128456282689546953 12633587346342212017160215)
                ·
                  refine ⟨18950381019513318025740323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12633587346342212017160215 18950381019513318025740323)
                  ·
                    refine ⟨28425571529269977038610485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18950381019513318025740323 28425571529269977038610485)
                    ·
                      refine ⟨2664897330869060347369733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28425571529269977038610485 2664897330869060347369733)
                      ·
                        rfl

theorem cell23_5189869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5189869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189869 prefixEnd_5189869 := by exact prefixLift 5189869
  have htrace : WordTrace (prefixWord ++ tailWord_5189869) baseStart_5189869 baseEnd_5189869 := by
    simpa [prefixWord, tailWord_5189869, baseEnd_5189869] using wordTrace_append hprefix tailTrace_5189869
  have hstable : (prefixWord ++ tailWord_5189869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189869).length < 2 ^ (prefixWord ++ tailWord_5189869).sum := by decide
  have hdescent : baseEnd_5189869 < baseStart_5189869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189885 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_5189885 : Nat := 118140960795 + 5189885 * 2 ^ 59
def prefixEnd_5189885 : Nat := 4983230072969 + 3 ^ 40 * 5189885 * 2
def baseEnd_5189885 : Nat := 888301848853177428256553

theorem tailTrace_5189885 : CollatzResearch.WordTrace tailWord_5189885 prefixEnd_5189885 888301848853177428256553 := by
  unfold tailWord_5189885
  simp only [CollatzResearch.WordTrace]
  refine ⟨189290656802940481636243109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126193771201960321090828739 189290656802940481636243109)
  ·
    refine ⟨35491998150551340306795583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189290656802940481636243109 35491998150551340306795583)
    ·
      refine ⟨53237997225827010460193375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35491998150551340306795583 53237997225827010460193375)
      ·
        refine ⟨79856995838740515690290063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53237997225827010460193375 79856995838740515690290063)
        ·
          refine ⟨119785493758110773535435095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79856995838740515690290063 119785493758110773535435095)
          ·
            refine ⟨179678240637166160303152643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119785493758110773535435095 179678240637166160303152643)
            ·
              refine ⟨269517360955749240454728965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179678240637166160303152643 269517360955749240454728965)
              ·
                refine ⟨50534505179202982585261681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269517360955749240454728965 50534505179202982585261681)
                ·
                  refine ⟨37900878884402236938946261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50534505179202982585261681 37900878884402236938946261)
                  ·
                    refine ⟨888301848853177428256553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37900878884402236938946261 888301848853177428256553)
                    ·
                      rfl

theorem cell23_5189885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_5189885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189885 prefixEnd_5189885 := by exact prefixLift 5189885
  have htrace : WordTrace (prefixWord ++ tailWord_5189885) baseStart_5189885 baseEnd_5189885 := by
    simpa [prefixWord, tailWord_5189885, baseEnd_5189885] using wordTrace_append hprefix tailTrace_5189885
  have hstable : (prefixWord ++ tailWord_5189885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189885).length < 2 ^ (prefixWord ++ tailWord_5189885).sum := by decide
  have hdescent : baseEnd_5189885 < baseStart_5189885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189886 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_5189886 : Nat := 118140960795 + 5189886 * 2 ^ 59
def prefixEnd_5189886 : Nat := 4983230072969 + 3 ^ 40 * 5189886 * 2
def baseEnd_5189886 : Nat := 2664906060040186780857155

theorem tailTrace_5189886 : CollatzResearch.WordTrace tailWord_5189886 prefixEnd_5189886 2664906060040186780857155 := by
  unfold tailWord_5189886
  simp only [CollatzResearch.WordTrace]
  refine ⟨23661336659492107350878689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126193795517291239204686341 23661336659492107350878689)
  ·
    refine ⟨17746002494619080513159017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23661336659492107350878689 17746002494619080513159017)
    ·
      refine ⟨13309501870964310384869263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17746002494619080513159017 13309501870964310384869263)
      ·
        refine ⟨19964252806446465577303895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13309501870964310384869263 19964252806446465577303895)
        ·
          refine ⟨29946379209669698365955843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19964252806446465577303895 29946379209669698365955843)
          ·
            refine ⟨44919568814504547548933765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29946379209669698365955843 44919568814504547548933765)
            ·
              refine ⟨8422419152719602665425081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44919568814504547548933765 8422419152719602665425081)
              ·
                refine ⟨6316814364539701999068811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8422419152719602665425081 6316814364539701999068811)
                ·
                  refine ⟨9475221546809552998603217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316814364539701999068811 9475221546809552998603217)
                  ·
                    refine ⟨7106416160107164748952413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9475221546809552998603217 7106416160107164748952413)
                    ·
                      refine ⟨2664906060040186780857155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106416160107164748952413 2664906060040186780857155)
                      ·
                        rfl

theorem cell23_5189886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_5189886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189886 prefixEnd_5189886 := by exact prefixLift 5189886
  have htrace : WordTrace (prefixWord ++ tailWord_5189886) baseStart_5189886 baseEnd_5189886 := by
    simpa [prefixWord, tailWord_5189886, baseEnd_5189886] using wordTrace_append hprefix tailTrace_5189886
  have hstable : (prefixWord ++ tailWord_5189886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189886).length < 2 ^ (prefixWord ++ tailWord_5189886).sum := by decide
  have hdescent : baseEnd_5189886 < baseStart_5189886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189915 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 4, 6]
def baseStart_5189915 : Nat := 118140960795 + 5189915 * 2 ^ 59
def prefixEnd_5189915 : Nat := 4983230072969 + 3 ^ 40 * 5189915 * 2
def baseEnd_5189915 : Nat := 888306983659722389131507

theorem tailTrace_5189915 : CollatzResearch.WordTrace tailWord_5189915 prefixEnd_5189915 888306983659722389131507 := by
  unfold tailWord_5189915
  simp only [CollatzResearch.WordTrace]
  refine ⟨189291750992831796759835199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126194500661887864506556799 189291750992831796759835199)
  ·
    refine ⟨283937626489247695139752799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189291750992831796759835199 283937626489247695139752799)
    ·
      refine ⟨425906439733871542709629199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283937626489247695139752799 425906439733871542709629199)
      ·
        refine ⟨638859659600807314064443799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425906439733871542709629199 638859659600807314064443799)
        ·
          refine ⟨958289489401210971096665699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638859659600807314064443799 958289489401210971096665699)
          ·
            refine ⟨1437434234101816456644998549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958289489401210971096665699 1437434234101816456644998549)
            ·
              refine ⟨67379729723522646405234307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1437434234101816456644998549 67379729723522646405234307)
              ·
                refine ⟨101069594585283969607851461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67379729723522646405234307 101069594585283969607851461)
                ·
                  refine ⟨18950548984740744301472149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101069594585283969607851461 18950548984740744301472149)
                  ·
                    refine ⟨888306983659722389131507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18950548984740744301472149 888306983659722389131507)
                    ·
                      rfl

theorem cell23_5189915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_5189915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189915 prefixEnd_5189915 := by exact prefixLift 5189915
  have htrace : WordTrace (prefixWord ++ tailWord_5189915) baseStart_5189915 baseEnd_5189915 := by
    simpa [prefixWord, tailWord_5189915, baseEnd_5189915] using wordTrace_append hprefix tailTrace_5189915
  have hstable : (prefixWord ++ tailWord_5189915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189915).length < 2 ^ (prefixWord ++ tailWord_5189915).sum := by decide
  have hdescent : baseEnd_5189915 < baseStart_5189915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189917 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5189917 : Nat := 118140960795 + 5189917 * 2 ^ 59
def prefixEnd_5189917 : Nat := 4983230072969 + 3 ^ 40 * 5189917 * 2
def baseEnd_5189917 : Nat := 2664921977940476159569513

theorem tailTrace_5189917 : CollatzResearch.WordTrace tailWord_5189917 prefixEnd_5189917 2664921977940476159569513 := by
  unfold tailWord_5189917
  simp only [CollatzResearch.WordTrace]
  refine ⟨189291823938824551101408005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126194549292549700734272003 189291823938824551101408005)
  ·
    refine ⟨35492216988529603331514001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189291823938824551101408005 35492216988529603331514001)
    ·
      refine ⟨26619162741397202498635501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35492216988529603331514001 26619162741397202498635501)
      ·
        refine ⟨9982186028023950936988313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26619162741397202498635501 9982186028023950936988313)
        ·
          refine ⟨7486639521017963202741235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9982186028023950936988313 7486639521017963202741235)
          ·
            refine ⟨11229959281526944804111853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7486639521017963202741235 11229959281526944804111853)
            ·
              refine ⟨4211234730572604301541945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11229959281526944804111853 4211234730572604301541945)
              ·
                refine ⟨3158426047929453226156459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211234730572604301541945 3158426047929453226156459)
                ·
                  refine ⟨4737639071894179839234689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158426047929453226156459 4737639071894179839234689)
                  ·
                    refine ⟨3553229303920634879426017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737639071894179839234689 3553229303920634879426017)
                    ·
                      refine ⟨2664921977940476159569513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553229303920634879426017 2664921977940476159569513)
                      ·
                        rfl

theorem cell23_5189917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5189917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189917 prefixEnd_5189917 := by exact prefixLift 5189917
  have htrace : WordTrace (prefixWord ++ tailWord_5189917) baseStart_5189917 baseEnd_5189917 := by
    simpa [prefixWord, tailWord_5189917, baseEnd_5189917] using wordTrace_append hprefix tailTrace_5189917
  have hstable : (prefixWord ++ tailWord_5189917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189917).length < 2 ^ (prefixWord ++ tailWord_5189917).sum := by decide
  have hdescent : baseEnd_5189917 < baseStart_5189917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189927 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5189927 : Nat := 118140960795 + 5189927 * 2 ^ 59
def prefixEnd_5189927 : Nat := 4983230072969 + 3 ^ 40 * 5189927 * 2
def baseEnd_5189927 : Nat := 888309037582340373481489

theorem tailTrace_5189927 : CollatzResearch.WordTrace tailWord_5189927 prefixEnd_5189927 888309037582340373481489 := by
  unfold tailWord_5189927
  simp only [CollatzResearch.WordTrace]
  refine ⟨189292188668788322809272035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126194792445858881872848023 189292188668788322809272035)
  ·
    refine ⟨283938283003182484213908053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189292188668788322809272035 283938283003182484213908053)
    ·
      refine ⟨3327401753943544736881735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 283938283003182484213908053 3327401753943544736881735)
      ·
        refine ⟨4991102630915317105322603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327401753943544736881735 4991102630915317105322603)
        ·
          refine ⟨7486653946372975657983905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991102630915317105322603 7486653946372975657983905)
          ·
            refine ⟨5614990459779731743487929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7486653946372975657983905 5614990459779731743487929)
            ·
              refine ⟨4211242844834798807615947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5614990459779731743487929 4211242844834798807615947)
              ·
                refine ⟨6316864267252198211423921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211242844834798807615947 6316864267252198211423921)
                ·
                  refine ⟨4737648200439148658567941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6316864267252198211423921 4737648200439148658567941)
                  ·
                    refine ⟨888309037582340373481489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737648200439148658567941 888309037582340373481489)
                    ·
                      rfl

theorem cell23_5189927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5189927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189927 prefixEnd_5189927 := by exact prefixLift 5189927
  have htrace : WordTrace (prefixWord ++ tailWord_5189927) baseStart_5189927 baseEnd_5189927 := by
    simpa [prefixWord, tailWord_5189927, baseEnd_5189927] using wordTrace_append hprefix tailTrace_5189927
  have hstable : (prefixWord ++ tailWord_5189927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189927).length < 2 ^ (prefixWord ++ tailWord_5189927).sum := by decide
  have hdescent : baseEnd_5189927 < baseStart_5189927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189939 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 1, 4, 2]
def baseStart_5189939 : Nat := 118140960795 + 5189939 * 2 ^ 59
def prefixEnd_5189939 : Nat := 4983230072969 + 3 ^ 40 * 5189939 * 2
def baseEnd_5189939 : Nat := 2664933274514875073494411

theorem tailTrace_5189939 : CollatzResearch.WordTrace tailWord_5189939 prefixEnd_5189939 2664933274514875073494411 := by
  unfold tailWord_5189939
  simp only [CollatzResearch.WordTrace]
  refine ⟨189292626344744848858708871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126195084229829899239139247 189292626344744848858708871)
  ·
    refine ⟨283938939517117273288063307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189292626344744848858708871 283938939517117273288063307)
    ·
      refine ⟨425908409275675909932094961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283938939517117273288063307 425908409275675909932094961)
      ·
        refine ⟨319431306956756932449071221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425908409275675909932094961 319431306956756932449071221)
        ·
          refine ⟨29946685027195962417100427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 319431306956756932449071221 29946685027195962417100427)
          ·
            refine ⟨44920027540793943625650641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29946685027195962417100427 44920027540793943625650641)
            ·
              refine ⟨33690020655595457719237981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44920027540793943625650641 33690020655595457719237981)
              ·
                refine ⟨12633757745848296644714243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33690020655595457719237981 12633757745848296644714243)
                ·
                  refine ⟨18950636618772444967071365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12633757745848296644714243 18950636618772444967071365)
                  ·
                    refine ⟨3553244366019833431325881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18950636618772444967071365 3553244366019833431325881)
                    ·
                      refine ⟨2664933274514875073494411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553244366019833431325881 2664933274514875073494411)
                      ·
                        rfl

theorem cell23_5189939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 4, 2].length) (baseStart_5189939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189939 prefixEnd_5189939 := by exact prefixLift 5189939
  have htrace : WordTrace (prefixWord ++ tailWord_5189939) baseStart_5189939 baseEnd_5189939 := by
    simpa [prefixWord, tailWord_5189939, baseEnd_5189939] using wordTrace_append hprefix tailTrace_5189939
  have hstable : (prefixWord ++ tailWord_5189939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189939).length < 2 ^ (prefixWord ++ tailWord_5189939).sum := by decide
  have hdescent : baseEnd_5189939 < baseStart_5189939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189989 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_5189989 : Nat := 118140960795 + 5189989 * 2 ^ 59
def prefixEnd_5189989 : Nat := 4983230072969 + 3 ^ 40 * 5189989 * 2
def baseEnd_5189989 : Nat := 2664958948547599877869181

theorem tailTrace_5189989 : CollatzResearch.WordTrace tailWord_5189989 prefixEnd_5189989 2664958948547599877869181 := by
  unfold tailWord_5189989
  simp only [CollatzResearch.WordTrace]
  refine ⟨189294449994563707398029021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126196299996375804932019347 189294449994563707398029021)
  ·
    refine ⟨70985418747961390274260883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189294449994563707398029021 70985418747961390274260883)
    ·
      refine ⟨106478128121942085411391325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70985418747961390274260883 106478128121942085411391325)
      ·
        refine ⟨39929298045728282029271747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106478128121942085411391325 39929298045728282029271747)
        ·
          refine ⟨59893947068592423043907621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39929298045728282029271747 59893947068592423043907621)
          ·
            refine ⟨11230115075361079320732679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59893947068592423043907621 11230115075361079320732679)
            ·
              refine ⟨16845172613041618981099019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11230115075361079320732679 16845172613041618981099019)
              ·
                refine ⟨25267758919562428471648529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16845172613041618981099019 25267758919562428471648529)
                ·
                  refine ⟨18950819189671821353736397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25267758919562428471648529 18950819189671821353736397)
                  ·
                    refine ⟨7106557196126933007651149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18950819189671821353736397 7106557196126933007651149)
                    ·
                      refine ⟨2664958948547599877869181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106557196126933007651149 2664958948547599877869181)
                      ·
                        rfl

theorem cell23_5189989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_5189989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189989 prefixEnd_5189989 := by exact prefixLift 5189989
  have htrace : WordTrace (prefixWord ++ tailWord_5189989) baseStart_5189989 baseEnd_5189989 := by
    simpa [prefixWord, tailWord_5189989, baseEnd_5189989] using wordTrace_append hprefix tailTrace_5189989
  have hstable : (prefixWord ++ tailWord_5189989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189989).length < 2 ^ (prefixWord ++ tailWord_5189989).sum := by decide
  have hdescent : baseEnd_5189989 < baseStart_5189989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190032 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_5190032 : Nat := 118140960795 + 5190032 * 2 ^ 59
def prefixEnd_5190032 : Nat := 4983230072969 + 3 ^ 40 * 5190032 * 2
def baseEnd_5190032 : Nat := 2664981028215743209631483

theorem tailTrace_5190032 : CollatzResearch.WordTrace tailWord_5190032 prefixEnd_5190032 2664981028215743209631483 := by
  unfold tailWord_5190032
  simp only [CollatzResearch.WordTrace]
  refine ⟨94648009166703962870922175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126197345555605283827896233 94648009166703962870922175)
  ·
    refine ⟨141972013750055944306383263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94648009166703962870922175 141972013750055944306383263)
    ·
      refine ⟨212958020625083916459574895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141972013750055944306383263 212958020625083916459574895)
      ·
        refine ⟨319437030937625874689362343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212958020625083916459574895 319437030937625874689362343)
        ·
          refine ⟨479155546406438812034043515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319437030937625874689362343 479155546406438812034043515)
          ·
            refine ⟨718733319609658218051065273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479155546406438812034043515 718733319609658218051065273)
            ·
              refine ⟨539049989707243663538298955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718733319609658218051065273 539049989707243663538298955)
              ·
                refine ⟨808574984560865495307448433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539049989707243663538298955 808574984560865495307448433)
                ·
                  refine ⟨606431238420649121480586325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808574984560865495307448433 606431238420649121480586325)
                  ·
                    refine ⟨7106616075241981892350621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 606431238420649121480586325 7106616075241981892350621)
                    ·
                      refine ⟨2664981028215743209631483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106616075241981892350621 2664981028215743209631483)
                      ·
                        rfl

theorem cell23_5190032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_5190032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190032 prefixEnd_5190032 := by exact prefixLift 5190032
  have htrace : WordTrace (prefixWord ++ tailWord_5190032) baseStart_5190032 baseEnd_5190032 := by
    simpa [prefixWord, tailWord_5190032, baseEnd_5190032] using wordTrace_append hprefix tailTrace_5190032
  have hstable : (prefixWord ++ tailWord_5190032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190032).length < 2 ^ (prefixWord ++ tailWord_5190032).sum := by decide
  have hdescent : baseEnd_5190032 < baseStart_5190032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190039 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 3, 4]
def baseStart_5190039 : Nat := 118140960795 + 5190039 * 2 ^ 59
def prefixEnd_5190039 : Nat := 4983230072969 + 3 ^ 40 * 5190039 * 2
def baseEnd_5190039 : Nat := 888328207526774894081317

theorem tailTrace_5190039 : CollatzResearch.WordTrace tailWord_5190039 prefixEnd_5190039 888328207526774894081317 := by
  unfold tailWord_5190039
  simp only [CollatzResearch.WordTrace]
  refine ⟨189296273644382565937349171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126197515762921710624899447 189296273644382565937349171)
  ·
    refine ⟨283944410466573848906023757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189296273644382565937349171 283944410466573848906023757)
    ·
      refine ⟨106479153924965193339758909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283944410466573848906023757 106479153924965193339758909)
      ·
        refine ⟨39929682721861947502409591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106479153924965193339758909 39929682721861947502409591)
        ·
          refine ⟨59894524082792921253614387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39929682721861947502409591 59894524082792921253614387)
          ·
            refine ⟨89841786124189381880421581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59894524082792921253614387 89841786124189381880421581)
            ·
              refine ⟨33690669796571018205158093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89841786124189381880421581 33690669796571018205158093)
              ·
                refine ⟨12634001173714131826934285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33690669796571018205158093 12634001173714131826934285)
                ·
                  refine ⟨4737750440142799435100357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12634001173714131826934285 4737750440142799435100357)
                  ·
                    refine ⟨888328207526774894081317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737750440142799435100357 888328207526774894081317)
                    ·
                      rfl

theorem cell23_5190039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_5190039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190039 prefixEnd_5190039 := by exact prefixLift 5190039
  have htrace : WordTrace (prefixWord ++ tailWord_5190039) baseStart_5190039 baseEnd_5190039 := by
    simpa [prefixWord, tailWord_5190039, baseEnd_5190039] using wordTrace_append hprefix tailTrace_5190039
  have hstable : (prefixWord ++ tailWord_5190039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190039).length < 2 ^ (prefixWord ++ tailWord_5190039).sum := by decide
  have hdescent : baseEnd_5190039 < baseStart_5190039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190046 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5190046 : Nat := 118140960795 + 5190046 * 2 ^ 59
def prefixEnd_5190046 : Nat := 4983230072969 + 3 ^ 40 * 5190046 * 2
def baseEnd_5190046 : Nat := 2664988216944906154856419

theorem tailTrace_5190046 : CollatzResearch.WordTrace tailWord_5190046 prefixEnd_5190046 2664988216944906154856419 := by
  unfold tailWord_5190046
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662066119419650766606749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126197685970238137421902661 23662066119419650766606749)
  ·
    refine ⟨8873274794782369037477531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23662066119419650766606749 8873274794782369037477531)
    ·
      refine ⟨13309912192173553556216297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8873274794782369037477531 13309912192173553556216297)
      ·
        refine ⟨9982434144130165167162223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13309912192173553556216297 9982434144130165167162223)
        ·
          refine ⟨14973651216195247750743335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982434144130165167162223 14973651216195247750743335)
          ·
            refine ⟨22460476824292871626115003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14973651216195247750743335 22460476824292871626115003)
            ·
              refine ⟨33690715236439307439172505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22460476824292871626115003 33690715236439307439172505)
              ·
                refine ⟨25268036427329480579379379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33690715236439307439172505 25268036427329480579379379)
                ·
                  refine ⟨37902054640994220869069069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25268036427329480579379379 37902054640994220869069069)
                  ·
                    refine ⟨14213270490372832825900901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37902054640994220869069069 14213270490372832825900901)
                    ·
                      refine ⟨2664988216944906154856419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14213270490372832825900901 2664988216944906154856419)
                      ·
                        rfl

theorem cell23_5190046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5190046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190046 prefixEnd_5190046 := by exact prefixLift 5190046
  have htrace : WordTrace (prefixWord ++ tailWord_5190046) baseStart_5190046 baseEnd_5190046 := by
    simpa [prefixWord, tailWord_5190046, baseEnd_5190046] using wordTrace_append hprefix tailTrace_5190046
  have hstable : (prefixWord ++ tailWord_5190046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190046).length < 2 ^ (prefixWord ++ tailWord_5190046).sum := by decide
  have hdescent : baseEnd_5190046 < baseStart_5190046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190073 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 1, 4]
def baseStart_5190073 : Nat := 118140960795 + 5190073 * 2 ^ 59
def prefixEnd_5190073 : Nat := 4983230072969 + 3 ^ 40 * 5190073 * 2
def baseEnd_5190073 : Nat := 888334026974192516406265

theorem tailTrace_5190073 : CollatzResearch.WordTrace tailWord_5190073 prefixEnd_5190073 888334026974192516406265 := by
  unfold tailWord_5190073
  simp only [CollatzResearch.WordTrace]
  refine ⟨189297513726259389744086873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126198342484172926496057915 189297513726259389744086873)
  ·
    refine ⟨141973135294694542308065155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189297513726259389744086873 141973135294694542308065155)
    ·
      refine ⟨212959702942041813462097733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141973135294694542308065155 212959702942041813462097733)
      ·
        refine ⟨39929944301632840024143325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212959702942041813462097733 39929944301632840024143325)
        ·
          refine ⟨14973729113112315009053747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39929944301632840024143325 14973729113112315009053747)
          ·
            refine ⟨22460593669668472513580621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14973729113112315009053747 22460593669668472513580621)
            ·
              refine ⟨8422722626125677192592733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22460593669668472513580621 8422722626125677192592733)
              ·
                refine ⟨3158520984797128947222275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8422722626125677192592733 3158520984797128947222275)
                ·
                  refine ⟨4737781477195693420833413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158520984797128947222275 4737781477195693420833413)
                  ·
                    refine ⟨888334026974192516406265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737781477195693420833413 888334026974192516406265)
                    ·
                      rfl

theorem cell23_5190073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 4].length) (baseStart_5190073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190073 prefixEnd_5190073 := by exact prefixLift 5190073
  have htrace : WordTrace (prefixWord ++ tailWord_5190073) baseStart_5190073 baseEnd_5190073 := by
    simpa [prefixWord, tailWord_5190073, baseEnd_5190073] using wordTrace_append hprefix tailTrace_5190073
  have hstable : (prefixWord ++ tailWord_5190073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190073).length < 2 ^ (prefixWord ++ tailWord_5190073).sum := by decide
  have hdescent : baseEnd_5190073 < baseStart_5190073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190106 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2]
def baseStart_5190106 : Nat := 118140960795 + 5190106 * 2 ^ 59
def prefixEnd_5190106 : Nat := 4983230072969 + 3 ^ 40 * 5190106 * 2
def baseEnd_5190106 : Nat := 2665019025784175920106143

theorem tailTrace_5190106 : CollatzResearch.WordTrace tailWord_5190106 prefixEnd_5190106 2665019025784175920106143 := by
  unfold tailWord_5190106
  simp only [CollatzResearch.WordTrace]
  refine ⟨47324679333784959095009543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126199144890093224253358781 47324679333784959095009543)
  ·
    refine ⟨70987019000677438642514315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47324679333784959095009543 70987019000677438642514315)
    ·
      refine ⟨106480528501016157963771473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70987019000677438642514315 106480528501016157963771473)
      ·
        refine ⟨79860396375762118472828605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106480528501016157963771473 79860396375762118472828605)
        ·
          refine ⟨29947648640910794427310727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79860396375762118472828605 29947648640910794427310727)
          ·
            refine ⟨44921472961366191640966091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29947648640910794427310727 44921472961366191640966091)
            ·
              refine ⟨67382209442049287461449137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44921472961366191640966091 67382209442049287461449137)
              ·
                refine ⟨50536657081536965596086853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67382209442049287461449137 50536657081536965596086853)
                ·
                  refine ⟨9475623202788181049266285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50536657081536965596086853 9475623202788181049266285)
                  ·
                    refine ⟨3553358701045567893474857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9475623202788181049266285 3553358701045567893474857)
                    ·
                      refine ⟨2665019025784175920106143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553358701045567893474857 2665019025784175920106143)
                      ·
                        rfl

theorem cell23_5190106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_5190106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190106 prefixEnd_5190106 := by exact prefixLift 5190106
  have htrace : WordTrace (prefixWord ++ tailWord_5190106) baseStart_5190106 baseEnd_5190106 := by
    simpa [prefixWord, tailWord_5190106, baseEnd_5190106] using wordTrace_append hprefix tailTrace_5190106
  have hstable : (prefixWord ++ tailWord_5190106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190106).length < 2 ^ (prefixWord ++ tailWord_5190106).sum := by decide
  have hdescent : baseEnd_5190106 < baseStart_5190106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190129 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_5190129 : Nat := 118140960795 + 5190129 * 2 ^ 59
def prefixEnd_5190129 : Nat := 4983230072969 + 3 ^ 40 * 5190129 * 2
def baseEnd_5190129 : Nat := 888343611946409776706179

theorem tailTrace_5190129 : CollatzResearch.WordTrace tailWord_5190129 prefixEnd_5190129 888343611946409776706179 := by
  unfold tailWord_5190129
  simp only [CollatzResearch.WordTrace]
  refine ⟨189299556214056511308125441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126199704142704340872083627 189299556214056511308125441)
  ·
    refine ⟨141974667160542383481094081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189299556214056511308125441 141974667160542383481094081)
    ·
      refine ⟨106481000370406787610820561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141974667160542383481094081 106481000370406787610820561)
      ·
        refine ⟨79860750277805090708115421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106481000370406787610820561 79860750277805090708115421)
        ·
          refine ⟨29947781354176909015543283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79860750277805090708115421 29947781354176909015543283)
          ·
            refine ⟨44921672031265363523314925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29947781354176909015543283 44921672031265363523314925)
            ·
              refine ⟨16845627011724511321243097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44921672031265363523314925 16845627011724511321243097)
              ·
                refine ⟨12634220258793383490932323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16845627011724511321243097 12634220258793383490932323)
                ·
                  refine ⟨18951330388190075236398485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12634220258793383490932323 18951330388190075236398485)
                  ·
                    refine ⟨888343611946409776706179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18951330388190075236398485 888343611946409776706179)
                    ·
                      rfl

theorem cell23_5190129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_5190129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190129 prefixEnd_5190129 := by exact prefixLift 5190129
  have htrace : WordTrace (prefixWord ++ tailWord_5190129) baseStart_5190129 baseEnd_5190129 := by
    simpa [prefixWord, tailWord_5190129, baseEnd_5190129] using wordTrace_append hprefix tailTrace_5190129
  have hstable : (prefixWord ++ tailWord_5190129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190129).length < 2 ^ (prefixWord ++ tailWord_5190129).sum := by decide
  have hdescent : baseEnd_5190129 < baseStart_5190129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190139 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 3]
def baseStart_5190139 : Nat := 118140960795 + 5190139 * 2 ^ 59
def prefixEnd_5190139 : Nat := 4983230072969 + 3 ^ 40 * 5190139 * 2
def baseEnd_5190139 : Nat := 2665035970645774290993491

theorem tailTrace_5190139 : CollatzResearch.WordTrace tailWord_5190139 prefixEnd_5190139 2665035970645774290993491 := by
  unfold tailWord_5190139
  simp only [CollatzResearch.WordTrace]
  refine ⟨189299920944020283015989471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126199947296013522010659647 189299920944020283015989471)
  ·
    refine ⟨283949881416030424523984207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189299920944020283015989471 283949881416030424523984207)
    ·
      refine ⟨425924822124045636785976311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283949881416030424523984207 425924822124045636785976311)
      ·
        refine ⟨638887233186068455178964467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425924822124045636785976311 638887233186068455178964467)
        ·
          refine ⟨958330849779102682768446701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638887233186068455178964467 958330849779102682768446701)
          ·
            refine ⟨359374068667163506038167513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 958330849779102682768446701 359374068667163506038167513)
            ·
              refine ⟨269530551500372629528625635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359374068667163506038167513 269530551500372629528625635)
              ·
                refine ⟨404295827250558944292938453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269530551500372629528625635 404295827250558944292938453)
                ·
                  refine ⟨9475683451184975256865745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 404295827250558944292938453 9475683451184975256865745)
                  ·
                    refine ⟨7106762588388731442649309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9475683451184975256865745 7106762588388731442649309)
                    ·
                      refine ⟨2665035970645774290993491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106762588388731442649309 2665035970645774290993491)
                      ·
                        rfl

theorem cell23_5190139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 3].length) (baseStart_5190139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190139 prefixEnd_5190139 := by exact prefixLift 5190139
  have htrace : WordTrace (prefixWord ++ tailWord_5190139) baseStart_5190139 baseEnd_5190139 := by
    simpa [prefixWord, tailWord_5190139, baseEnd_5190139] using wordTrace_append hprefix tailTrace_5190139
  have hstable : (prefixWord ++ tailWord_5190139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190139).length < 2 ^ (prefixWord ++ tailWord_5190139).sum := by decide
  have hdescent : baseEnd_5190139 < baseStart_5190139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190150 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5190150 : Nat := 118140960795 + 5190150 * 2 ^ 59
def prefixEnd_5190150 : Nat := 4983230072969 + 3 ^ 40 * 5190150 * 2
def baseEnd_5190150 : Nat := 888347206310991249318647

theorem tailTrace_5190150 : CollatzResearch.WordTrace tailWord_5190150 prefixEnd_5190150 888347206310991249318647 := by
  unfold tailWord_5190150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915635067093138496707497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126200214764653621263093269 5915635067093138496707497)
  ·
    refine ⟨4436726300319853872530623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5915635067093138496707497 4436726300319853872530623)
    ·
      refine ⟨6655089450479780808795935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4436726300319853872530623 6655089450479780808795935)
      ·
        refine ⟨9982634175719671213193903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6655089450479780808795935 9982634175719671213193903)
        ·
          refine ⟨14973951263579506819790855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982634175719671213193903 14973951263579506819790855)
          ·
            refine ⟨22460926895369260229686283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14973951263579506819790855 22460926895369260229686283)
            ·
              refine ⟨33691390343053890344529425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22460926895369260229686283 33691390343053890344529425)
              ·
                refine ⟨25268542757290417758397069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33691390343053890344529425 25268542757290417758397069)
                ·
                  refine ⟨9475703533983906659398901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25268542757290417758397069 9475703533983906659398901)
                  ·
                    refine ⟨888347206310991249318647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9475703533983906659398901 888347206310991249318647)
                    ·
                      rfl

theorem cell23_5190150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5190150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190150 prefixEnd_5190150 := by exact prefixLift 5190150
  have htrace : WordTrace (prefixWord ++ tailWord_5190150) baseStart_5190150 baseEnd_5190150 := by
    simpa [prefixWord, tailWord_5190150, baseEnd_5190150] using wordTrace_append hprefix tailTrace_5190150
  have hstable : (prefixWord ++ tailWord_5190150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190150).length < 2 ^ (prefixWord ++ tailWord_5190150).sum := by decide
  have hdescent : baseEnd_5190150 < baseStart_5190150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190156 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_5190156 : Nat := 118140960795 + 5190156 * 2 ^ 59
def prefixEnd_5190156 : Nat := 4983230072969 + 3 ^ 40 * 5190156 * 2
def baseEnd_5190156 : Nat := 2665044699816900724480913

theorem tailTrace_5190156 : CollatzResearch.WordTrace tailWord_5190156 prefixEnd_5190156 2665044699816900724480913 := by
  unfold tailWord_5190156
  simp only [CollatzResearch.WordTrace]
  refine ⟨94650270492479347459679161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126200360656639129946238881 94650270492479347459679161)
  ·
    refine ⟨70987702869359510594759371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94650270492479347459679161 70987702869359510594759371)
    ·
      refine ⟨106481554304039265892139057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70987702869359510594759371 106481554304039265892139057)
      ·
        refine ⟨79861165728029449419104293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106481554304039265892139057 79861165728029449419104293)
        ·
          refine ⟨14973968574005521766082055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79861165728029449419104293 14973968574005521766082055)
          ·
            refine ⟨22460952861008282649123083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14973968574005521766082055 22460952861008282649123083)
            ·
              refine ⟨33691429291512423973684625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22460952861008282649123083 33691429291512423973684625)
              ·
                refine ⟨25268571968634317980263469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33691429291512423973684625 25268571968634317980263469)
                ·
                  refine ⟨9475714488237869242598801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25268571968634317980263469 9475714488237869242598801)
                  ·
                    refine ⟨7106785866178401931949101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9475714488237869242598801 7106785866178401931949101)
                    ·
                      refine ⟨2665044699816900724480913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106785866178401931949101 2665044699816900724480913)
                      ·
                        rfl

theorem cell23_5190156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_5190156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190156 prefixEnd_5190156 := by exact prefixLift 5190156
  have htrace : WordTrace (prefixWord ++ tailWord_5190156) baseStart_5190156 baseEnd_5190156 := by
    simpa [prefixWord, tailWord_5190156, baseEnd_5190156] using wordTrace_append hprefix tailTrace_5190156
  have hstable : (prefixWord ++ tailWord_5190156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190156).length < 2 ^ (prefixWord ++ tailWord_5190156).sum := by decide
  have hdescent : baseEnd_5190156 < baseStart_5190156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190169 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_5190169 : Nat := 118140960795 + 5190169 * 2 ^ 59
def prefixEnd_5190169 : Nat := 4983230072969 + 3 ^ 40 * 5190169 * 2
def baseEnd_5190169 : Nat := 2665051375065409173618353

theorem tailTrace_5190169 : CollatzResearch.WordTrace tailWord_5190169 prefixEnd_5190169 2665051375065409173618353 := by
  unfold tailWord_5190169
  simp only [CollatzResearch.WordTrace]
  refine ⟨189301015133911598139581561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126200676755941065426387707 189301015133911598139581561)
  ·
    refine ⟨141975761350433698604686171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189301015133911598139581561 141975761350433698604686171)
    ·
      refine ⟨212963642025650547907029257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141975761350433698604686171 212963642025650547907029257)
      ·
        refine ⟨159722731519237910930271943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212963642025650547907029257 159722731519237910930271943)
        ·
          refine ⟨239584097278856866395407915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159722731519237910930271943 239584097278856866395407915)
          ·
            refine ⟨359376145918285299593111873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239584097278856866395407915 359376145918285299593111873)
            ·
              refine ⟨269532109438713974694833905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359376145918285299593111873 269532109438713974694833905)
              ·
                refine ⟨202149082079035481021125429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269532109438713974694833905 202149082079035481021125429)
                ·
                  refine ⟨18951476444909576345730509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202149082079035481021125429 18951476444909576345730509)
                  ·
                    refine ⟨7106803666841091129648941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18951476444909576345730509 7106803666841091129648941)
                    ·
                      refine ⟨2665051375065409173618353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106803666841091129648941 2665051375065409173618353)
                      ·
                        rfl

theorem cell23_5190169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_5190169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190169 prefixEnd_5190169 := by exact prefixLift 5190169
  have htrace : WordTrace (prefixWord ++ tailWord_5190169) baseStart_5190169 baseEnd_5190169 := by
    simpa [prefixWord, tailWord_5190169, baseEnd_5190169] using wordTrace_append hprefix tailTrace_5190169
  have hstable : (prefixWord ++ tailWord_5190169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190169).length < 2 ^ (prefixWord ++ tailWord_5190169).sum := by decide
  have hdescent : baseEnd_5190169 < baseStart_5190169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190190 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_5190190 : Nat := 118140960795 + 5190190 * 2 ^ 59
def prefixEnd_5190190 : Nat := 4983230072969 + 3 ^ 40 * 5190190 * 2
def baseEnd_5190190 : Nat := 2665062158159153591455757

theorem tailTrace_5190190 : CollatzResearch.WordTrace tailWord_5190190 prefixEnd_5190190 2665062158159153591455757 := by
  unfold tailWord_5190190
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662722633354439840762003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126201187377890345817397349 23662722633354439840762003)
  ·
    refine ⟨35494083950031659761143005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23662722633354439840762003 35494083950031659761143005)
    ·
      refine ⟨13310281481261872410428627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35494083950031659761143005 13310281481261872410428627)
      ·
        refine ⟨19965422221892808615642941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13310281481261872410428627 19965422221892808615642941)
        ·
          refine ⟨7487033333209803230866103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19965422221892808615642941 7487033333209803230866103)
          ·
            refine ⟨11230549999814704846299155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7487033333209803230866103 11230549999814704846299155)
            ·
              refine ⟨16845824999722057269448733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11230549999814704846299155 16845824999722057269448733)
              ·
                refine ⟨6317184374895771476043275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16845824999722057269448733 6317184374895771476043275)
                ·
                  refine ⟨9475776562343657214064913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6317184374895771476043275 9475776562343657214064913)
                  ·
                    refine ⟨7106832421757742910548685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9475776562343657214064913 7106832421757742910548685)
                    ·
                      refine ⟨2665062158159153591455757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106832421757742910548685 2665062158159153591455757)
                      ·
                        rfl

theorem cell23_5190190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_5190190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190190 prefixEnd_5190190 := by exact prefixLift 5190190
  have htrace : WordTrace (prefixWord ++ tailWord_5190190) baseStart_5190190 baseEnd_5190190 := by
    simpa [prefixWord, tailWord_5190190, baseEnd_5190190] using wordTrace_append hprefix tailTrace_5190190
  have hstable : (prefixWord ++ tailWord_5190190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190190).length < 2 ^ (prefixWord ++ tailWord_5190190).sum := by decide
  have hdescent : baseEnd_5190190 < baseStart_5190190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190219 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 2, 6]
def baseStart_5190219 : Nat := 118140960795 + 5190219 * 2 ^ 59
def prefixEnd_5190219 : Nat := 4983230072969 + 3 ^ 40 * 5190219 * 2
def baseEnd_5190219 : Nat := 888359016366044659331041

theorem tailTrace_5190219 : CollatzResearch.WordTrace tailWord_5190219 prefixEnd_5190219 888359016366044659331041 := by
  unfold tailWord_5190219
  simp only [CollatzResearch.WordTrace]
  refine ⟨189302838783730456678901711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126201892522486971119267807 189302838783730456678901711)
  ·
    refine ⟨283954258175595685018352567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189302838783730456678901711 283954258175595685018352567)
    ·
      refine ⟨425931387263393527527528851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283954258175595685018352567 425931387263393527527528851)
      ·
        refine ⟨638897080895090291291293277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425931387263393527527528851 638897080895090291291293277)
        ·
          refine ⟨239586405335658859234234979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638897080895090291291293277 239586405335658859234234979)
          ·
            refine ⟨359379608003488288851352469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239586405335658859234234979 359379608003488288851352469)
            ·
              refine ⟨16845919125163513539907147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 359379608003488288851352469 16845919125163513539907147)
              ·
                refine ⟨25268878687745270309860721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16845919125163513539907147 25268878687745270309860721)
                ·
                  refine ⟨18951659015808952732395541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25268878687745270309860721 18951659015808952732395541)
                  ·
                    refine ⟨888359016366044659331041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18951659015808952732395541 888359016366044659331041)
                    ·
                      rfl

theorem cell23_5190219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_5190219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190219 prefixEnd_5190219 := by exact prefixLift 5190219
  have htrace : WordTrace (prefixWord ++ tailWord_5190219) baseStart_5190219 baseEnd_5190219 := by
    simpa [prefixWord, tailWord_5190219, baseEnd_5190219] using wordTrace_append hprefix tailTrace_5190219
  have hstable : (prefixWord ++ tailWord_5190219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190219).length < 2 ^ (prefixWord ++ tailWord_5190219).sum := by decide
  have hdescent : baseEnd_5190219 < baseStart_5190219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190220 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 2, 1, 3]
def baseStart_5190220 : Nat := 118140960795 + 5190220 * 2 ^ 59
def prefixEnd_5190220 : Nat := 4983230072969 + 3 ^ 40 * 5190220 * 2
def baseEnd_5190220 : Nat := 2665077562578788474080619

theorem tailTrace_5190220 : CollatzResearch.WordTrace tailWord_5190220 prefixEnd_5190220 2665077562578788474080619 := by
  unfold tailWord_5190220
  simp only [CollatzResearch.WordTrace]
  refine ⟨94651437628363416924844057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126201916837817889233125409 94651437628363416924844057)
  ·
    refine ⟨70988578221272562693633043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94651437628363416924844057 70988578221272562693633043)
    ·
      refine ⟨106482867331908844040449565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70988578221272562693633043 106482867331908844040449565)
      ·
        refine ⟨39931075249465816515168587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106482867331908844040449565 39931075249465816515168587)
        ·
          refine ⟨59896612874198724772752881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39931075249465816515168587 59896612874198724772752881)
          ·
            refine ⟨44922459655649043579564661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59896612874198724772752881 44922459655649043579564661)
            ·
              refine ⟨4211480592717097835584187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44922459655649043579564661 4211480592717097835584187)
              ·
                refine ⟨6317220889075646753376281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211480592717097835584187 6317220889075646753376281)
                ·
                  refine ⟨4737915666806735065032211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6317220889075646753376281 4737915666806735065032211)
                  ·
                    refine ⟨7106873500210102597548317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4737915666806735065032211 7106873500210102597548317)
                    ·
                      refine ⟨2665077562578788474080619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106873500210102597548317 2665077562578788474080619)
                      ·
                        rfl

theorem cell23_5190220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_5190220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190220 prefixEnd_5190220 := by exact prefixLift 5190220
  have htrace : WordTrace (prefixWord ++ tailWord_5190220) baseStart_5190220 baseEnd_5190220 := by
    simpa [prefixWord, tailWord_5190220, baseEnd_5190220] using wordTrace_append hprefix tailTrace_5190220
  have hstable : (prefixWord ++ tailWord_5190220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190220).length < 2 ^ (prefixWord ++ tailWord_5190220).sum := by decide
  have hdescent : baseEnd_5190220 < baseStart_5190220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190239 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_5190239 : Nat := 118140960795 + 5190239 * 2 ^ 59
def prefixEnd_5190239 : Nat := 4983230072969 + 3 ^ 40 * 5190239 * 2
def baseEnd_5190239 : Nat := 2665087318711223899743031

theorem tailTrace_5190239 : CollatzResearch.WordTrace tailWord_5190239 prefixEnd_5190239 2665087318711223899743031 := by
  unfold tailWord_5190239
  simp only [CollatzResearch.WordTrace]
  refine ⟨189303568243658000094629771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126202378829105333396419847 189303568243658000094629771)
  ·
    refine ⟨283955352365487000141944657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189303568243658000094629771 283955352365487000141944657)
    ·
      refine ⟨212966514274115250106458493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283955352365487000141944657 212966514274115250106458493)
      ·
        refine ⟨79862442852793218789921935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212966514274115250106458493 79862442852793218789921935)
        ·
          refine ⟨119793664279189828184882903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79862442852793218789921935 119793664279189828184882903)
          ·
            refine ⟨179690496418784742277324355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119793664279189828184882903 179690496418784742277324355)
            ·
              refine ⟨269535744628177113415986533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179690496418784742277324355 269535744628177113415986533)
              ·
                refine ⟨50537952117783208765497475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269535744628177113415986533 50537952117783208765497475)
                ·
                  refine ⟨75806928176674813148246213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50537952117783208765497475 75806928176674813148246213)
                  ·
                    refine ⟨14213799033126527465296165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75806928176674813148246213 14213799033126527465296165)
                    ·
                      refine ⟨2665087318711223899743031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14213799033126527465296165 2665087318711223899743031)
                      ·
                        rfl

theorem cell23_5190239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_5190239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190239 prefixEnd_5190239 := by exact prefixLift 5190239
  have htrace : WordTrace (prefixWord ++ tailWord_5190239) baseStart_5190239 baseEnd_5190239 := by
    simpa [prefixWord, tailWord_5190239, baseEnd_5190239] using wordTrace_append hprefix tailTrace_5190239
  have hstable : (prefixWord ++ tailWord_5190239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190239).length < 2 ^ (prefixWord ++ tailWord_5190239).sum := by decide
  have hdescent : baseEnd_5190239 < baseStart_5190239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190243 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 6, 2, 2]
def baseStart_5190243 : Nat := 118140960795 + 5190243 * 2 ^ 59
def prefixEnd_5190243 : Nat := 4983230072969 + 3 ^ 40 * 5190243 * 2
def baseEnd_5190243 : Nat := 2665089372633841884093013

theorem tailTrace_5190243 : CollatzResearch.WordTrace tailWord_5190243 prefixEnd_5190243 2665089372633841884093013 := by
  unfold tailWord_5190243
  simp only [CollatzResearch.WordTrace]
  refine ⟨189303714135643508777775383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126202476090429005851850255 189303714135643508777775383)
  ·
    refine ⟨283955571203465263166663075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189303714135643508777775383 283955571203465263166663075)
    ·
      refine ⟨425933356805197894749994613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283955571203465263166663075 425933356805197894749994613)
      ·
        refine ⟨39931252200487302632811995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 425933356805197894749994613 39931252200487302632811995)
        ·
          refine ⟨59896878300730953949217993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39931252200487302632811995 59896878300730953949217993)
          ·
            refine ⟨44922658725548215461913495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59896878300730953949217993 44922658725548215461913495)
            ·
              refine ⟨67383988088322323192870243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44922658725548215461913495 67383988088322323192870243)
              ·
                refine ⟨101075982132483484789305365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67383988088322323192870243 101075982132483484789305365)
                ·
                  refine ⟨4737936662460163349498689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101075982132483484789305365 4737936662460163349498689)
                  ·
                    refine ⟨3553452496845122512124017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737936662460163349498689 3553452496845122512124017)
                    ·
                      refine ⟨2665089372633841884093013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553452496845122512124017 2665089372633841884093013)
                      ·
                        rfl

theorem cell23_5190243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_5190243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190243 prefixEnd_5190243 := by exact prefixLift 5190243
  have htrace : WordTrace (prefixWord ++ tailWord_5190243) baseStart_5190243 baseEnd_5190243 := by
    simpa [prefixWord, tailWord_5190243, baseEnd_5190243] using wordTrace_append hprefix tailTrace_5190243
  have hstable : (prefixWord ++ tailWord_5190243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190243).length < 2 ^ (prefixWord ++ tailWord_5190243).sum := by decide
  have hdescent : baseEnd_5190243 < baseStart_5190243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190277 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 2, 2, 2]
def baseStart_5190277 : Nat := 118140960795 + 5190277 * 2 ^ 59
def prefixEnd_5190277 : Nat := 4983230072969 + 3 ^ 40 * 5190277 * 2
def baseEnd_5190277 : Nat := 2665106830976094751067857

theorem tailTrace_5190277 : CollatzResearch.WordTrace tailWord_5190277 prefixEnd_5190277 2665106830976094751067857 := by
  unfold tailWord_5190277
  simp only [CollatzResearch.WordTrace]
  refine ⟨189304954217520332584513085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126203302811680221723008723 189304954217520332584513085)
  ·
    refine ⟨70989357831570124719192407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189304954217520332584513085 70989357831570124719192407)
    ·
      refine ⟨106484036747355187078788611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70989357831570124719192407 106484036747355187078788611)
      ·
        refine ⟨159726055121032780618182917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106484036747355187078788611 159726055121032780618182917)
        ·
          refine ⟨29948635335193646365909297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159726055121032780618182917 29948635335193646365909297)
          ·
            refine ⟨22461476501395234774431973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29948635335193646365909297 22461476501395234774431973)
            ·
              refine ⟨4211526844011606520205995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22461476501395234774431973 4211526844011606520205995)
              ·
                refine ⟨6317290266017409780308993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211526844011606520205995 6317290266017409780308993)
                ·
                  refine ⟨4737967699513057335231745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6317290266017409780308993 4737967699513057335231745)
                  ·
                    refine ⟨3553475774634793001423809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737967699513057335231745 3553475774634793001423809)
                    ·
                      refine ⟨2665106830976094751067857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553475774634793001423809 2665106830976094751067857)
                      ·
                        rfl

theorem cell23_5190277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_5190277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190277 prefixEnd_5190277 := by exact prefixLift 5190277
  have htrace : WordTrace (prefixWord ++ tailWord_5190277) baseStart_5190277 baseEnd_5190277 := by
    simpa [prefixWord, tailWord_5190277, baseEnd_5190277] using wordTrace_append hprefix tailTrace_5190277
  have hstable : (prefixWord ++ tailWord_5190277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190277).length < 2 ^ (prefixWord ++ tailWord_5190277).sum := by decide
  have hdescent : baseEnd_5190277 < baseStart_5190277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190317 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 5]
def baseStart_5190317 : Nat := 118140960795 + 5190317 * 2 ^ 59
def prefixEnd_5190317 : Nat := 4983230072969 + 3 ^ 40 * 5190317 * 2
def baseEnd_5190317 : Nat := 296125263355808288285297

theorem tailTrace_5190317 : CollatzResearch.WordTrace tailWord_5190317 prefixEnd_5190317 296125263355808288285297 := by
  unfold tailWord_5190317
  simp only [CollatzResearch.WordTrace]
  refine ⟨189306413137375419415969205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126204275424916946277312803 189306413137375419415969205)
  ·
    refine ⟨17747476231628945570247113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189306413137375419415969205 17747476231628945570247113)
    ·
      refine ⟨13310607173721709177685335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17747476231628945570247113 13310607173721709177685335)
      ·
        refine ⟨19965910760582563766528003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13310607173721709177685335 19965910760582563766528003)
        ·
          refine ⟨29948866140873845649792005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19965910760582563766528003 29948866140873845649792005)
          ·
            refine ⟨5615412401413846059336001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29948866140873845649792005 5615412401413846059336001)
            ·
              refine ⟨4211559301060384544502001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5615412401413846059336001 4211559301060384544502001)
              ·
                refine ⟨3158669475795288408376501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211559301060384544502001 3158669475795288408376501)
                ·
                  refine ⟨296125263355808288285297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3158669475795288408376501 296125263355808288285297)
                  ·
                    rfl

theorem cell23_5190317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_5190317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190317 prefixEnd_5190317 := by exact prefixLift 5190317
  have htrace : WordTrace (prefixWord ++ tailWord_5190317) baseStart_5190317 baseEnd_5190317 := by
    simpa [prefixWord, tailWord_5190317, baseEnd_5190317] using wordTrace_append hprefix tailTrace_5190317
  have hstable : (prefixWord ++ tailWord_5190317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190317).length < 2 ^ (prefixWord ++ tailWord_5190317).sum := by decide
  have hdescent : baseEnd_5190317 < baseStart_5190317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190333 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_5190333 : Nat := 118140960795 + 5190333 * 2 ^ 59
def prefixEnd_5190333 : Nat := 4983230072969 + 3 ^ 40 * 5190333 * 2
def baseEnd_5190333 : Nat := 2665135585892746531967599

theorem tailTrace_5190333 : CollatzResearch.WordTrace tailWord_5190333 prefixEnd_5190333 2665135585892746531967599 := by
  unfold tailWord_5190333
  simp only [CollatzResearch.WordTrace]
  refine ⟨189306996705317454148551653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126204664470211636099034435 189306996705317454148551653)
  ·
    refine ⟨35495061882247022652853435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189306996705317454148551653 35495061882247022652853435)
    ·
      refine ⟨53242592823370533979280153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35495061882247022652853435 53242592823370533979280153)
      ·
        refine ⟨39931944617527900484460115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53242592823370533979280153 39931944617527900484460115)
        ·
          refine ⟨59897916926291850726690173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39931944617527900484460115 59897916926291850726690173)
          ·
            refine ⟨22461718847359444022508815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59897916926291850726690173 22461718847359444022508815)
            ·
              refine ⟨33692578271039166033763223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22461718847359444022508815 33692578271039166033763223)
              ·
                refine ⟨50538867406558749050644835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33692578271039166033763223 50538867406558749050644835)
                ·
                  refine ⟨75808301109838123575967253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50538867406558749050644835 75808301109838123575967253)
                  ·
                    refine ⟨3553514114523662042623465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75808301109838123575967253 3553514114523662042623465)
                    ·
                      refine ⟨2665135585892746531967599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553514114523662042623465 2665135585892746531967599)
                      ·
                        rfl

theorem cell23_5190333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_5190333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190333 prefixEnd_5190333 := by exact prefixLift 5190333
  have htrace : WordTrace (prefixWord ++ tailWord_5190333) baseStart_5190333 baseEnd_5190333 := by
    simpa [prefixWord, tailWord_5190333, baseEnd_5190333] using wordTrace_append hprefix tailTrace_5190333
  have hstable : (prefixWord ++ tailWord_5190333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190333).length < 2 ^ (prefixWord ++ tailWord_5190333).sum := by decide
  have hdescent : baseEnd_5190333 < baseStart_5190333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190350 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_5190350 : Nat := 118140960795 + 5190350 * 2 ^ 59
def prefixEnd_5190350 : Nat := 4983230072969 + 3 ^ 40 * 5190350 * 2
def baseEnd_5190350 : Nat := 2665144315063872965455021

theorem tailTrace_5190350 : CollatzResearch.WordTrace tailWord_5190350 prefixEnd_5190350 2665144315063872965455021 := by
  unfold tailWord_5190350
  simp only [CollatzResearch.WordTrace]
  refine ⟨23663452093281983256490063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126205077830837244034613669 23663452093281983256490063)
  ·
    refine ⟨35495178139922974884735095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23663452093281983256490063 35495178139922974884735095)
    ·
      refine ⟨53242767209884462327102643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35495178139922974884735095 53242767209884462327102643)
      ·
        refine ⟨79864150814826693490653965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53242767209884462327102643 79864150814826693490653965)
        ·
          refine ⟨29949056555560010058995237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79864150814826693490653965 29949056555560010058995237)
          ·
            refine ⟨5615448104167501886061607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29949056555560010058995237 5615448104167501886061607)
            ·
              refine ⟨8423172156251252829092411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5615448104167501886061607 8423172156251252829092411)
              ·
                refine ⟨12634758234376879243638617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8423172156251252829092411 12634758234376879243638617)
                ·
                  refine ⟨9476068675782659432728963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12634758234376879243638617 9476068675782659432728963)
                  ·
                    refine ⟨14214103013673989149093445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9476068675782659432728963 14214103013673989149093445)
                    ·
                      refine ⟨2665144315063872965455021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14214103013673989149093445 2665144315063872965455021)
                      ·
                        rfl

theorem cell23_5190350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_5190350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190350 prefixEnd_5190350 := by exact prefixLift 5190350
  have htrace : WordTrace (prefixWord ++ tailWord_5190350) baseStart_5190350 baseEnd_5190350 := by
    simpa [prefixWord, tailWord_5190350, baseEnd_5190350] using wordTrace_append hprefix tailTrace_5190350
  have hstable : (prefixWord ++ tailWord_5190350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190350).length < 2 ^ (prefixWord ++ tailWord_5190350).sum := by decide
  have hdescent : baseEnd_5190350 < baseStart_5190350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190360 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 1, 4]
def baseStart_5190360 : Nat := 118140960795 + 5190360 * 2 ^ 59
def prefixEnd_5190360 : Nat := 4983230072969 + 3 ^ 40 * 5190360 * 2
def baseEnd_5190360 : Nat := 888383149956805975443325

theorem tailTrace_5190360 : CollatzResearch.WordTrace tailWord_5190360 prefixEnd_5190360 888383149956805975443325 := by
  unfold tailWord_5190360
  simp only [CollatzResearch.WordTrace]
  refine ⟨94653990738109818879892267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126205320984146425173189689 94653990738109818879892267)
  ·
    refine ⟨141980986107164728319838401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94653990738109818879892267 141980986107164728319838401)
    ·
      refine ⟨106485739580373546239878801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141980986107164728319838401 106485739580373546239878801)
      ·
        refine ⟨79864304685280159679909101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106485739580373546239878801 79864304685280159679909101)
        ·
          refine ⟨29949114256980059879965913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79864304685280159679909101 29949114256980059879965913)
          ·
            refine ⟨22461835692735044909974435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29949114256980059879965913 22461835692735044909974435)
            ·
              refine ⟨33692753539102567364961653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22461835692735044909974435 33692753539102567364961653)
              ·
                refine ⟨3158695644290865690465155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33692753539102567364961653 3158695644290865690465155)
                ·
                  refine ⟨4738043466436298535697733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158695644290865690465155 4738043466436298535697733)
                  ·
                    refine ⟨888383149956805975443325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738043466436298535697733 888383149956805975443325)
                    ·
                      rfl

theorem cell23_5190360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_5190360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190360 prefixEnd_5190360 := by exact prefixLift 5190360
  have htrace : WordTrace (prefixWord ++ tailWord_5190360) baseStart_5190360 baseEnd_5190360 := by
    simpa [prefixWord, tailWord_5190360, baseEnd_5190360] using wordTrace_append hprefix tailTrace_5190360
  have hstable : (prefixWord ++ tailWord_5190360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190360).length < 2 ^ (prefixWord ++ tailWord_5190360).sum := by decide
  have hdescent : baseEnd_5190360 < baseStart_5190360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190373 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 6]
def baseStart_5190373 : Nat := 118140960795 + 5190373 * 2 ^ 59
def prefixEnd_5190373 : Nat := 4983230072969 + 3 ^ 40 * 5190373 * 2
def baseEnd_5190373 : Nat := 296128458346547375051935

theorem tailTrace_5190373 : CollatzResearch.WordTrace tailWord_5190373 prefixEnd_5190373 296128458346547375051935 := by
  unfold tailWord_5190373
  simp only [CollatzResearch.WordTrace]
  refine ⟨189308455625172540980007773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126205637083448360653338515 189308455625172540980007773)
  ·
    refine ⟨70990670859439702867502915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189308455625172540980007773 70990670859439702867502915)
    ·
      refine ⟨106486006289159554301254373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70990670859439702867502915 106486006289159554301254373)
      ·
        refine ⟨19966126179217416431485195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106486006289159554301254373 19966126179217416431485195)
        ·
          refine ⟨29949189268826124647227793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19966126179217416431485195 29949189268826124647227793)
          ·
            refine ⟨22461891951619593485420845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29949189268826124647227793 22461891951619593485420845)
            ·
              refine ⟨8423209481857347557032817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22461891951619593485420845 8423209481857347557032817)
              ·
                refine ⟨6317407111393010667774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8423209481857347557032817 6317407111393010667774613)
                ·
                  refine ⟨296128458346547375051935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6317407111393010667774613 296128458346547375051935)
                  ·
                    rfl

theorem cell23_5190373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_5190373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190373 prefixEnd_5190373 := by exact prefixLift 5190373
  have htrace : WordTrace (prefixWord ++ tailWord_5190373) baseStart_5190373 baseEnd_5190373 := by
    simpa [prefixWord, tailWord_5190373, baseEnd_5190373] using wordTrace_append hprefix tailTrace_5190373
  have hstable : (prefixWord ++ tailWord_5190373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190373).length < 2 ^ (prefixWord ++ tailWord_5190373).sum := by decide
  have hdescent : baseEnd_5190373 < baseStart_5190373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190390 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_5190390 : Nat := 118140960795 + 5190390 * 2 ^ 59
def prefixEnd_5190390 : Nat := 4983230072969 + 3 ^ 40 * 5190390 * 2
def baseEnd_5190390 : Nat := 296129428254450312106093

theorem tailTrace_5190390 : CollatzResearch.WordTrace tailWord_5190390 prefixEnd_5190390 296129428254450312106093 := by
  unfold tailWord_5190390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11831817229131934555211039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126206050444073968588917749 11831817229131934555211039)
  ·
    refine ⟨17747725843697901832816559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11831817229131934555211039 17747725843697901832816559)
    ·
      refine ⟨26621588765546852749224839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17747725843697901832816559 26621588765546852749224839)
      ·
        refine ⟨39932383148320279123837259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26621588765546852749224839 39932383148320279123837259)
        ·
          refine ⟨59898574722480418685755889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39932383148320279123837259 59898574722480418685755889)
          ·
            refine ⟨44923931041860314014316917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59898574722480418685755889 44923931041860314014316917)
            ·
              refine ⟨4211618535174404438842211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44923931041860314014316917 4211618535174404438842211)
              ·
                refine ⟨6317427802761606658263317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4211618535174404438842211 6317427802761606658263317)
                ·
                  refine ⟨296129428254450312106093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6317427802761606658263317 296129428254450312106093)
                  ·
                    rfl

theorem cell23_5190390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_5190390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190390 prefixEnd_5190390 := by exact prefixLift 5190390
  have htrace : WordTrace (prefixWord ++ tailWord_5190390) baseStart_5190390 baseEnd_5190390 := by
    simpa [prefixWord, tailWord_5190390, baseEnd_5190390] using wordTrace_append hprefix tailTrace_5190390
  have hstable : (prefixWord ++ tailWord_5190390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190390).length < 2 ^ (prefixWord ++ tailWord_5190390).sum := by decide
  have hdescent : baseEnd_5190390 < baseStart_5190390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190410 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_5190410 : Nat := 118140960795 + 5190410 * 2 ^ 59
def prefixEnd_5190410 : Nat := 4983230072969 + 3 ^ 40 * 5190410 * 2
def baseEnd_5190410 : Nat := 2665175123903142730704745

theorem tailTrace_5190410 : CollatzResearch.WordTrace tailWord_5190410 prefixEnd_5190410 2665175123903142730704745 := by
  unfold tailWord_5190410
  simp only [CollatzResearch.WordTrace]
  refine ⟨47327451281509624074776171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126206536750692330866069789 47327451281509624074776171)
  ·
    refine ⟨70991176922264436112164257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47327451281509624074776171 70991176922264436112164257)
    ·
      refine ⟨53243382691698327084123193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70991176922264436112164257 53243382691698327084123193)
      ·
        refine ⟨39932537018773745313092395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53243382691698327084123193 39932537018773745313092395)
        ·
          refine ⟨59898805528160617969638593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39932537018773745313092395 59898805528160617969638593)
          ·
            refine ⟨44924104146120463477228945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59898805528160617969638593 44924104146120463477228945)
            ·
              refine ⟨33693078109590347607921709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44924104146120463477228945 33693078109590347607921709)
              ·
                refine ⟨12634904291096380352970641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33693078109590347607921709 12634904291096380352970641)
                ·
                  refine ⟨9476178218322285264727981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12634904291096380352970641 9476178218322285264727981)
                  ·
                    refine ⟨3553566831870856974272993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9476178218322285264727981 3553566831870856974272993)
                    ·
                      refine ⟨2665175123903142730704745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553566831870856974272993 2665175123903142730704745)
                      ·
                        rfl

theorem cell23_5190410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_5190410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190410 prefixEnd_5190410 := by exact prefixLift 5190410
  have htrace : WordTrace (prefixWord ++ tailWord_5190410) baseStart_5190410 baseEnd_5190410 := by
    simpa [prefixWord, tailWord_5190410, baseEnd_5190410] using wordTrace_append hprefix tailTrace_5190410
  have hstable : (prefixWord ++ tailWord_5190410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190410).length < 2 ^ (prefixWord ++ tailWord_5190410).sum := by decide
  have hdescent : baseEnd_5190410 < baseStart_5190410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190417 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 1, 1, 3]
def baseStart_5190417 : Nat := 118140960795 + 5190417 * 2 ^ 59
def prefixEnd_5190417 : Nat := 4983230072969 + 3 ^ 40 * 5190417 * 2
def baseEnd_5190417 : Nat := 2665178718267724203317213

theorem tailTrace_5190417 : CollatzResearch.WordTrace tailWord_5190417 prefixEnd_5190417 2665178718267724203317213 := by
  unfold tailWord_5190417
  simp only [CollatzResearch.WordTrace]
  refine ⟨189310060437013136494609505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126206706958008757663073003 189310060437013136494609505)
  ·
    refine ⟨141982545327759852370957129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189310060437013136494609505 141982545327759852370957129)
    ·
      refine ⟨106486908995819889278217847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141982545327759852370957129 106486908995819889278217847)
      ·
        refine ⟨159730363493729833917326771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106486908995819889278217847 159730363493729833917326771)
        ·
          refine ⟨239595545240594750875990157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159730363493729833917326771 239595545240594750875990157)
          ·
            refine ⟨89848329465223031578496309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239595545240594750875990157 89848329465223031578496309)
            ·
              refine ⟨8423280887364659210484029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89848329465223031578496309 8423280887364659210484029)
              ·
                refine ⟨3158730332761747203931511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8423280887364659210484029 3158730332761747203931511)
                ·
                  refine ⟨4738095499142620805897267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158730332761747203931511 4738095499142620805897267)
                  ·
                    refine ⟨7107143248713931208845901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4738095499142620805897267 7107143248713931208845901)
                    ·
                      refine ⟨2665178718267724203317213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7107143248713931208845901 2665178718267724203317213)
                      ·
                        rfl

theorem cell23_5190417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_5190417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190417 prefixEnd_5190417 := by exact prefixLift 5190417
  have htrace : WordTrace (prefixWord ++ tailWord_5190417) baseStart_5190417 baseEnd_5190417 := by
    simpa [prefixWord, tailWord_5190417, baseEnd_5190417] using wordTrace_append hprefix tailTrace_5190417
  have hstable : (prefixWord ++ tailWord_5190417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190417).length < 2 ^ (prefixWord ++ tailWord_5190417).sum := by decide
  have hdescent : baseEnd_5190417 < baseStart_5190417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190433 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 4, 4]
def baseStart_5190433 : Nat := 118140960795 + 5190433 * 2 ^ 59
def prefixEnd_5190433 : Nat := 4983230072969 + 3 ^ 40 * 5190433 * 2
def baseEnd_5190433 : Nat := 888395644652732046905713

theorem tailTrace_5190433 : CollatzResearch.WordTrace tailWord_5190433 prefixEnd_5190433 888395644652732046905713 := by
  unfold tailWord_5190433
  simp only [CollatzResearch.WordTrace]
  refine ⟨189310644004955171227191953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126207096003303447484794635 189310644004955171227191953)
  ·
    refine ⟨141982983003716378420393965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189310644004955171227191953 141982983003716378420393965)
    ·
      refine ⟨53243618626393641907647737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141982983003716378420393965 53243618626393641907647737)
      ·
        refine ⟨39932713969795231430735803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53243618626393641907647737 39932713969795231430735803)
        ·
          refine ⟨59899070954692847146103705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39932713969795231430735803 59899070954692847146103705)
          ·
            refine ⟨44924303216019635359577779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59899070954692847146103705 44924303216019635359577779)
            ·
              refine ⟨67386454824029453039366669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44924303216019635359577779 67386454824029453039366669)
              ·
                refine ⟨25269920559011044889762501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67386454824029453039366669 25269920559011044889762501)
                ·
                  refine ⟨4738110104814570916830469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25269920559011044889762501 4738110104814570916830469)
                  ·
                    refine ⟨888395644652732046905713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738110104814570916830469 888395644652732046905713)
                    ·
                      rfl

theorem cell23_5190433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_5190433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190433 prefixEnd_5190433 := by exact prefixLift 5190433
  have htrace : WordTrace (prefixWord ++ tailWord_5190433) baseStart_5190433 baseEnd_5190433 := by
    simpa [prefixWord, tailWord_5190433, baseEnd_5190433] using wordTrace_append hprefix tailTrace_5190433
  have hstable : (prefixWord ++ tailWord_5190433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190433).length < 2 ^ (prefixWord ++ tailWord_5190433).sum := by decide
  have hdescent : baseEnd_5190433 < baseStart_5190433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190450 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_5190450 : Nat := 118140960795 + 5190450 * 2 ^ 59
def prefixEnd_5190450 : Nat := 4983230072969 + 3 ^ 40 * 5190450 * 2
def baseEnd_5190450 : Nat := 888398554376440858068187

theorem tailTrace_5190450 : CollatzResearch.WordTrace tailWord_5190450 prefixEnd_5190450 888398554376440858068187 := by
  unfold tailWord_5190450
  simp only [CollatzResearch.WordTrace]
  refine ⟨47327816011473395782640201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126207509363929055420373869 47327816011473395782640201)
  ·
    refine ⟨35495862008605046836980151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47327816011473395782640201 35495862008605046836980151)
    ·
      refine ⟨53243793012907570255470227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35495862008605046836980151 53243793012907570255470227)
      ·
        refine ⟨79865689519361355383205341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53243793012907570255470227 79865689519361355383205341)
        ·
          refine ⟨29949633569760508268702003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79865689519361355383205341 29949633569760508268702003)
          ·
            refine ⟨44924450354640762403053005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29949633569760508268702003 44924450354640762403053005)
            ·
              refine ⟨16846668882990285901144877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44924450354640762403053005 16846668882990285901144877)
              ·
                refine ⟨6317500831121357212929329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16846668882990285901144877 6317500831121357212929329)
                ·
                  refine ⟨4738125623341017909696997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6317500831121357212929329 4738125623341017909696997)
                  ·
                    refine ⟨888398554376440858068187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738125623341017909696997 888398554376440858068187)
                    ·
                      rfl

theorem cell23_5190450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_5190450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190450 prefixEnd_5190450 := by exact prefixLift 5190450
  have htrace : WordTrace (prefixWord ++ tailWord_5190450) baseStart_5190450 baseEnd_5190450 := by
    simpa [prefixWord, tailWord_5190450, baseEnd_5190450] using wordTrace_append hprefix tailTrace_5190450
  have hstable : (prefixWord ++ tailWord_5190450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190450).length < 2 ^ (prefixWord ++ tailWord_5190450).sum := by decide
  have hdescent : baseEnd_5190450 < baseStart_5190450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190453 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5190453 : Nat := 118140960795 + 5190453 * 2 ^ 59
def prefixEnd_5190453 : Nat := 4983230072969 + 3 ^ 40 * 5190453 * 2
def baseEnd_5190453 : Nat := 2665197203571286062467047

theorem tailTrace_5190453 : CollatzResearch.WordTrace tailWord_5190453 prefixEnd_5190453 2665197203571286062467047 := by
  unfold tailWord_5190453
  simp only [CollatzResearch.WordTrace]
  refine ⟨189311373464882714642920013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126207582309921809761946675 189311373464882714642920013)
  ·
    refine ⟨70991765049331017991095005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189311373464882714642920013 70991765049331017991095005)
    ·
      refine ⟨26621911893499131746660627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70991765049331017991095005 26621911893499131746660627)
      ·
        refine ⟨39932867840248697619990941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26621911893499131746660627 39932867840248697619990941)
        ·
          refine ⟨14974825440093261607496603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39932867840248697619990941 14974825440093261607496603)
          ·
            refine ⟨22462238160139892411244905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14974825440093261607496603 22462238160139892411244905)
            ·
              refine ⟨16846678620104919308433679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22462238160139892411244905 16846678620104919308433679)
              ·
                refine ⟨25270017930157378962650519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16846678620104919308433679 25270017930157378962650519)
                ·
                  refine ⟨37905026895236068443975779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25270017930157378962650519 37905026895236068443975779)
                  ·
                    refine ⟨56857540342854102665963669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37905026895236068443975779 56857540342854102665963669)
                    ·
                      refine ⟨2665197203571286062467047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56857540342854102665963669 2665197203571286062467047)
                      ·
                        rfl

theorem cell23_5190453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5190453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190453 prefixEnd_5190453 := by exact prefixLift 5190453
  have htrace : WordTrace (prefixWord ++ tailWord_5190453) baseStart_5190453 baseEnd_5190453 := by
    simpa [prefixWord, tailWord_5190453, baseEnd_5190453] using wordTrace_append hprefix tailTrace_5190453
  have hstable : (prefixWord ++ tailWord_5190453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190453).length < 2 ^ (prefixWord ++ tailWord_5190453).sum := by decide
  have hdescent : baseEnd_5190453 < baseStart_5190453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190454 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5190454 : Nat := 118140960795 + 5190454 * 2 ^ 59
def prefixEnd_5190454 : Nat := 4983230072969 + 3 ^ 40 * 5190454 * 2
def baseEnd_5190454 : Nat := 888399239017313519518181

theorem tailTrace_5190454 : CollatzResearch.WordTrace tailWord_5190454 prefixEnd_5190454 888399239017313519518181 := by
  unfold tailWord_5190454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11831963121117443238356651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126207606625252727875804277 11831963121117443238356651)
  ·
    refine ⟨17747944681676164857534977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11831963121117443238356651 17747944681676164857534977)
    ·
      refine ⟨13310958511257123643151233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17747944681676164857534977 13310958511257123643151233)
      ·
        refine ⟨9983218883442842732363425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13310958511257123643151233 9983218883442842732363425)
        ·
          refine ⟨7487414162582132049272569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9983218883442842732363425 7487414162582132049272569)
          ·
            refine ⟨5615560621936599036954427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7487414162582132049272569 5615560621936599036954427)
            ·
              refine ⟨8423340932904898555431641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5615560621936599036954427 8423340932904898555431641)
              ·
                refine ⟨6317505699678673916573731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8423340932904898555431641 6317505699678673916573731)
                ·
                  refine ⟨9476258549518010874860597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6317505699678673916573731 9476258549518010874860597)
                  ·
                    refine ⟨888399239017313519518181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9476258549518010874860597 888399239017313519518181)
                    ·
                      rfl

theorem cell23_5190454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5190454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190454 prefixEnd_5190454 := by exact prefixLift 5190454
  have htrace : WordTrace (prefixWord ++ tailWord_5190454) baseStart_5190454 baseEnd_5190454 := by
    simpa [prefixWord, tailWord_5190454, baseEnd_5190454] using wordTrace_append hprefix tailTrace_5190454
  have hstable : (prefixWord ++ tailWord_5190454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190454).length < 2 ^ (prefixWord ++ tailWord_5190454).sum := by decide
  have hdescent : baseEnd_5190454 < baseStart_5190454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190473 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_5190473 : Nat := 118140960795 + 5190473 * 2 ^ 59
def prefixEnd_5190473 : Nat := 4983230072969 + 3 ^ 40 * 5190473 * 2
def baseEnd_5190473 : Nat := 2665207473184375984216955

theorem tailTrace_5190473 : CollatzResearch.WordTrace tailWord_5190473 prefixEnd_5190473 2665207473184375984216955 := by
  unfold tailWord_5190473
  simp only [CollatzResearch.WordTrace]
  refine ⟨189312102924810258058648073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126208068616540172039098715 189312102924810258058648073)
  ·
    refine ⟨141984077193607693543986055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189312102924810258058648073 141984077193607693543986055)
    ·
      refine ⟨212976115790411540315979083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141984077193607693543986055 212976115790411540315979083)
      ·
        refine ⟨319464173685617310473968625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212976115790411540315979083 319464173685617310473968625)
        ·
          refine ⟨239598130264212982855476469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319464173685617310473968625 239598130264212982855476469)
          ·
            refine ⟨22462324712269967142700919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239598130264212982855476469 22462324712269967142700919)
            ·
              refine ⟨33693487068404950714051379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22462324712269967142700919 33693487068404950714051379)
              ·
                refine ⟨50540230602607426071077069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33693487068404950714051379 50540230602607426071077069)
                ·
                  refine ⟨18952586475977784776653901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50540230602607426071077069 18952586475977784776653901)
                  ·
                    refine ⟨7107219928491669291245213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18952586475977784776653901 7107219928491669291245213)
                    ·
                      refine ⟨2665207473184375984216955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7107219928491669291245213 2665207473184375984216955)
                      ·
                        rfl

theorem cell23_5190473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_5190473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190473 prefixEnd_5190473 := by exact prefixLift 5190473
  have htrace : WordTrace (prefixWord ++ tailWord_5190473) baseStart_5190473 baseEnd_5190473 := by
    simpa [prefixWord, tailWord_5190473, baseEnd_5190473] using wordTrace_append hprefix tailTrace_5190473
  have hstable : (prefixWord ++ tailWord_5190473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190473).length < 2 ^ (prefixWord ++ tailWord_5190473).sum := by decide
  have hdescent : baseEnd_5190473 < baseStart_5190473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190517 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_5190517 : Nat := 118140960795 + 5190517 * 2 ^ 59
def prefixEnd_5190517 : Nat := 4983230072969 + 3 ^ 40 * 5190517 * 2
def baseEnd_5190517 : Nat := 2665230066333173812066753

theorem tailTrace_5190517 : CollatzResearch.WordTrace tailWord_5190517 prefixEnd_5190517 2665230066333173812066753 := by
  unfold tailWord_5190517
  simp only [CollatzResearch.WordTrace]
  refine ⟨189313707736650853573249805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126209138491100569048833203 189313707736650853573249805)
  ·
    refine ⟨70992640401244070089968677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189313707736650853573249805 70992640401244070089968677)
    ·
      refine ⟨13311120075233263141869127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70992640401244070089968677 13311120075233263141869127)
      ·
        refine ⟨19966680112849894712803691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13311120075233263141869127 19966680112849894712803691)
        ·
          refine ⟨29950020169274842069205537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19966680112849894712803691 29950020169274842069205537)
          ·
            refine ⟨22462515126956131551904153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29950020169274842069205537 22462515126956131551904153)
            ·
              refine ⟨16846886345217098663928115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22462515126956131551904153 16846886345217098663928115)
              ·
                refine ⟨25270329517825647995892173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16846886345217098663928115 25270329517825647995892173)
                ·
                  refine ⟨9476373569184617998459565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25270329517825647995892173 9476373569184617998459565)
                  ·
                    refine ⟨3553640088444231749422337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9476373569184617998459565 3553640088444231749422337)
                    ·
                      refine ⟨2665230066333173812066753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553640088444231749422337 2665230066333173812066753)
                      ·
                        rfl

theorem cell23_5190517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_5190517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190517 prefixEnd_5190517 := by exact prefixLift 5190517
  have htrace : WordTrace (prefixWord ++ tailWord_5190517) baseStart_5190517 baseEnd_5190517 := by
    simpa [prefixWord, tailWord_5190517, baseEnd_5190517] using wordTrace_append hprefix tailTrace_5190517
  have hstable : (prefixWord ++ tailWord_5190517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190517).length < 2 ^ (prefixWord ++ tailWord_5190517).sum := by decide
  have hdescent : baseEnd_5190517 < baseStart_5190517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190547 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 2, 2, 2]
def baseStart_5190547 : Nat := 118140960795 + 5190547 * 2 ^ 59
def prefixEnd_5190547 : Nat := 4983230072969 + 3 ^ 40 * 5190547 * 2
def baseEnd_5190547 : Nat := 2665245470752808694691615

theorem tailTrace_5190547 : CollatzResearch.WordTrace tailWord_5190547 prefixEnd_5190547 2665245470752808694691615 := by
  unfold tailWord_5190547
  simp only [CollatzResearch.WordTrace]
  refine ⟨189314801926542168696841895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126209867951028112464561263 189314801926542168696841895)
  ·
    refine ⟨283972202889813253045262843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189314801926542168696841895 283972202889813253045262843)
    ·
      refine ⟨425958304334719879567894265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283972202889813253045262843 425958304334719879567894265)
      ·
        refine ⟨319468728251039909675920699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425958304334719879567894265 319468728251039909675920699)
        ·
          refine ⟨479203092376559864513881049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319468728251039909675920699 479203092376559864513881049)
          ·
            refine ⟨359402319282419898385410787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479203092376559864513881049 359402319282419898385410787)
            ·
              refine ⟨539103478923629847578116181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359402319282419898385410787 539103478923629847578116181)
              ·
                refine ⟨6317618893636287276306049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 539103478923629847578116181 6317618893636287276306049)
                ·
                  refine ⟨4738214170227215457229537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6317618893636287276306049 4738214170227215457229537)
                  ·
                    refine ⟨3553660627670411592922153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4738214170227215457229537 3553660627670411592922153)
                    ·
                      refine ⟨2665245470752808694691615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553660627670411592922153 2665245470752808694691615)
                      ·
                        rfl

theorem cell23_5190547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 2, 2].length) (baseStart_5190547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190547 prefixEnd_5190547 := by exact prefixLift 5190547
  have htrace : WordTrace (prefixWord ++ tailWord_5190547) baseStart_5190547 baseEnd_5190547 := by
    simpa [prefixWord, tailWord_5190547, baseEnd_5190547] using wordTrace_append hprefix tailTrace_5190547
  have hstable : (prefixWord ++ tailWord_5190547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190547).length < 2 ^ (prefixWord ++ tailWord_5190547).sum := by decide
  have hdescent : baseEnd_5190547 < baseStart_5190547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190583 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 1, 7]
def baseStart_5190583 : Nat := 118140960795 + 5190583 * 2 ^ 59
def prefixEnd_5190583 : Nat := 4983230072969 + 3 ^ 40 * 5190583 * 2
def baseEnd_5190583 : Nat := 888421318685456851280483

theorem tailTrace_5190583 : CollatzResearch.WordTrace tailWord_5190583 prefixEnd_5190583 888421318685456851280483 := by
  unfold tailWord_5190583
  simp only [CollatzResearch.WordTrace]
  refine ⟨189316114954411746845152403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126210743302941164563434935 189316114954411746845152403)
  ·
    refine ⟨283974172431617620267728605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189316114954411746845152403 283974172431617620267728605)
    ·
      refine ⟨106490314661856607600398227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283974172431617620267728605 106490314661856607600398227)
      ·
        refine ⟨159735471992784911400597341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106490314661856607600398227 159735471992784911400597341)
        ·
          refine ⟨59900801997294341775224003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159735471992784911400597341 59900801997294341775224003)
          ·
            refine ⟨89851202995941512662836005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59900801997294341775224003 89851202995941512662836005)
            ·
              refine ⟨16847100561739033624281751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89851202995941512662836005 16847100561739033624281751)
              ·
                refine ⟨25270650842608550436422627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16847100561739033624281751 25270650842608550436422627)
                ·
                  refine ⟨37905976263912825654633941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25270650842608550436422627 37905976263912825654633941)
                  ·
                    refine ⟨888421318685456851280483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37905976263912825654633941 888421318685456851280483)
                    ·
                      rfl

theorem cell23_5190583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_5190583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190583 prefixEnd_5190583 := by exact prefixLift 5190583
  have htrace : WordTrace (prefixWord ++ tailWord_5190583) baseStart_5190583 baseEnd_5190583 := by
    simpa [prefixWord, tailWord_5190583, baseEnd_5190583] using wordTrace_append hprefix tailTrace_5190583
  have hstable : (prefixWord ++ tailWord_5190583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190583).length < 2 ^ (prefixWord ++ tailWord_5190583).sum := by decide
  have hdescent : baseEnd_5190583 < baseStart_5190583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190610 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5190610 : Nat := 118140960795 + 5190610 * 2 ^ 59
def prefixEnd_5190610 : Nat := 4983230072969 + 3 ^ 40 * 5190610 * 2
def baseEnd_5190610 : Nat := 2665277820034041948203825

theorem tailTrace_5190610 : CollatzResearch.WordTrace tailWord_5190610 prefixEnd_5190610 2665277820034041948203825 := by
  unfold tailWord_5190610
  simp only [CollatzResearch.WordTrace]
  refine ⟨47329274931328482614096321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126211399816875953637590189 47329274931328482614096321)
  ·
    refine ⟨35496956198496361960572241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47329274931328482614096321 35496956198496361960572241)
    ·
      refine ⟨26622717148872271470429181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35496956198496361960572241 26622717148872271470429181)
      ·
        refine ⟨9983518930827101801410943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26622717148872271470429181 9983518930827101801410943)
        ·
          refine ⟨14975278396240652702116415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9983518930827101801410943 14975278396240652702116415)
          ·
            refine ⟨22462917594360979053174623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14975278396240652702116415 22462917594360979053174623)
            ·
              refine ⟨33694376391541468579761935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22462917594360979053174623 33694376391541468579761935)
              ·
                refine ⟨50541564587312202869642903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33694376391541468579761935 50541564587312202869642903)
                ·
                  refine ⟨75812346880968304304464355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50541564587312202869642903 75812346880968304304464355)
                  ·
                    refine ⟨113718520321452456456696533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75812346880968304304464355 113718520321452456456696533)
                    ·
                      refine ⟨2665277820034041948203825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113718520321452456456696533 2665277820034041948203825)
                      ·
                        rfl

theorem cell23_5190610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5190610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190610 prefixEnd_5190610 := by exact prefixLift 5190610
  have htrace : WordTrace (prefixWord ++ tailWord_5190610) baseStart_5190610 baseEnd_5190610 := by
    simpa [prefixWord, tailWord_5190610, baseEnd_5190610] using wordTrace_append hprefix tailTrace_5190610
  have hstable : (prefixWord ++ tailWord_5190610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190610).length < 2 ^ (prefixWord ++ tailWord_5190610).sum := by decide
  have hdescent : baseEnd_5190610 < baseStart_5190610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190657 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_5190657 : Nat := 118140960795 + 5190657 * 2 ^ 59
def prefixEnd_5190657 : Nat := 4983230072969 + 3 ^ 40 * 5190657 * 2
def baseEnd_5190657 : Nat := 2665301953624803264316109

theorem tailTrace_5190657 : CollatzResearch.WordTrace tailWord_5190657 prefixEnd_5190657 2665301953624803264316109 := by
  unfold tailWord_5190657
  simp only [CollatzResearch.WordTrace]
  refine ⟨189318813956143657483346225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126212542637429104988897483 189318813956143657483346225)
  ·
    refine ⟨141989110467107743112509669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189318813956143657483346225 141989110467107743112509669)
    ·
      refine ⟨26622958212582701833595563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141989110467107743112509669 26622958212582701833595563)
      ·
        refine ⟨39934437318874052750393345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26622958212582701833595563 39934437318874052750393345)
        ·
          refine ⟨29950827989155539562795009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39934437318874052750393345 29950827989155539562795009)
          ·
            refine ⟨22463120991866654672096257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29950827989155539562795009 22463120991866654672096257)
            ·
              refine ⟨16847340743899991004072193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22463120991866654672096257 16847340743899991004072193)
              ·
                refine ⟨12635505557924993253054145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16847340743899991004072193 12635505557924993253054145)
                ·
                  refine ⟨9476629168443744939790609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12635505557924993253054145 9476629168443744939790609)
                  ·
                    refine ⟨7107471876332808704842957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9476629168443744939790609 7107471876332808704842957)
                    ·
                      refine ⟨2665301953624803264316109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7107471876332808704842957 2665301953624803264316109)
                      ·
                        rfl

theorem cell23_5190657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_5190657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190657 prefixEnd_5190657 := by exact prefixLift 5190657
  have htrace : WordTrace (prefixWord ++ tailWord_5190657) baseStart_5190657 baseEnd_5190657 := by
    simpa [prefixWord, tailWord_5190657, baseEnd_5190657] using wordTrace_append hprefix tailTrace_5190657
  have hstable : (prefixWord ++ tailWord_5190657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190657).length < 2 ^ (prefixWord ++ tailWord_5190657).sum := by decide
  have hdescent : baseEnd_5190657 < baseStart_5190657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190664 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 1, 4]
def baseStart_5190664 : Nat := 118140960795 + 5190664 * 2 ^ 59
def prefixEnd_5190664 : Nat := 4983230072969 + 3 ^ 40 * 5190664 * 2
def baseEnd_5190664 : Nat := 888435182663128245642859

theorem tailTrace_5190664 : CollatzResearch.WordTrace tailWord_5190664 prefixEnd_5190664 888435182663128245642859 := by
  unfold tailWord_5190664
  simp only [CollatzResearch.WordTrace]
  refine ⟨94659534633559148839425523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126212712844745531785900697 94659534633559148839425523)
  ·
    refine ⟨141989301950338723259138285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94659534633559148839425523 141989301950338723259138285)
    ·
      refine ⟨53245988231377021222176857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141989301950338723259138285 53245988231377021222176857)
      ·
        refine ⟨39934491173532765916632643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53245988231377021222176857 39934491173532765916632643)
        ·
          refine ⟨59901736760299148874948965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39934491173532765916632643 59901736760299148874948965)
          ·
            refine ⟨11231575642556090414052931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59901736760299148874948965 11231575642556090414052931)
            ·
              refine ⟨16847363463834135621079397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11231575642556090414052931 16847363463834135621079397)
              ·
                refine ⟨3158880649468900428952387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16847363463834135621079397 3158880649468900428952387)
                ·
                  refine ⟨4738320974203350643428581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158880649468900428952387 4738320974203350643428581)
                  ·
                    refine ⟨888435182663128245642859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738320974203350643428581 888435182663128245642859)
                    ·
                      rfl

theorem cell23_5190664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_5190664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190664 prefixEnd_5190664 := by exact prefixLift 5190664
  have htrace : WordTrace (prefixWord ++ tailWord_5190664) baseStart_5190664 baseEnd_5190664 := by
    simpa [prefixWord, tailWord_5190664, baseEnd_5190664] using wordTrace_append hprefix tailTrace_5190664
  have hstable : (prefixWord ++ tailWord_5190664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190664).length < 2 ^ (prefixWord ++ tailWord_5190664).sum := by decide
  have hdescent : baseEnd_5190664 < baseStart_5190664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190683 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_5190683 : Nat := 118140960795 + 5190683 * 2 ^ 59
def prefixEnd_5190683 : Nat := 4983230072969 + 3 ^ 40 * 5190683 * 2
def baseEnd_5190683 : Nat := 2665315304121820162590989

theorem tailTrace_5190683 : CollatzResearch.WordTrace tailWord_5190683 prefixEnd_5190683 2665315304121820162590989 := by
  unfold tailWord_5190683
  simp only [CollatzResearch.WordTrace]
  refine ⟨189319762254049463923792703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126213174836032975949195135 189319762254049463923792703)
  ·
    refine ⟨283979643381074195885689055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189319762254049463923792703 283979643381074195885689055)
    ·
      refine ⟨425969465071611293828533583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283979643381074195885689055 425969465071611293828533583)
      ·
        refine ⟨638954197607416940742800375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425969465071611293828533583 638954197607416940742800375)
        ·
          refine ⟨958431296411125411114200563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638954197607416940742800375 958431296411125411114200563)
          ·
            refine ⟨1437646944616688116671300845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958431296411125411114200563 1437646944616688116671300845)
            ·
              refine ⟨539117604231258043751737817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1437646944616688116671300845 539117604231258043751737817)
              ·
                refine ⟨404338203173443532813803363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539117604231258043751737817 404338203173443532813803363)
                ·
                  refine ⟨606507304760165299220705045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404338203173443532813803363 606507304760165299220705045)
                  ·
                    refine ⟨28430029910632748400970549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 606507304760165299220705045 28430029910632748400970549)
                    ·
                      refine ⟨2665315304121820162590989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28430029910632748400970549 2665315304121820162590989)
                      ·
                        rfl

theorem cell23_5190683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_5190683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190683 prefixEnd_5190683 := by exact prefixLift 5190683
  have htrace : WordTrace (prefixWord ++ tailWord_5190683) baseStart_5190683 baseEnd_5190683 := by
    simpa [prefixWord, tailWord_5190683, baseEnd_5190683] using wordTrace_append hprefix tailTrace_5190683
  have hstable : (prefixWord ++ tailWord_5190683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190683).length < 2 ^ (prefixWord ++ tailWord_5190683).sum := by decide
  have hdescent : baseEnd_5190683 < baseStart_5190683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190687 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 3]
def baseStart_5190687 : Nat := 118140960795 + 5190687 * 2 ^ 59
def prefixEnd_5190687 : Nat := 4983230072969 + 3 ^ 40 * 5190687 * 2
def baseEnd_5190687 : Nat := 2665317358044438146940971

theorem tailTrace_5190687 : CollatzResearch.WordTrace tailWord_5190687 prefixEnd_5190687 2665317358044438146940971 := by
  unfold tailWord_5190687
  simp only [CollatzResearch.WordTrace]
  refine ⟨189319908146034972606938315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126213272097356648404625543 189319908146034972606938315)
  ·
    refine ⟨283979862219052458910407473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189319908146034972606938315 283979862219052458910407473)
    ·
      refine ⟨212984896664289344182805605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283979862219052458910407473 212984896664289344182805605)
      ·
        refine ⟨39934668124554252034276051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212984896664289344182805605 39934668124554252034276051)
        ·
          refine ⟨59902002186831378051414077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39934668124554252034276051 59902002186831378051414077)
          ·
            refine ⟨22463250820061766769280279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59902002186831378051414077 22463250820061766769280279)
            ·
              refine ⟨33694876230092650153920419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22463250820061766769280279 33694876230092650153920419)
              ·
                refine ⟨50542314345138975230880629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33694876230092650153920419 50542314345138975230880629)
                ·
                  refine ⟨4738341969856778927895059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50542314345138975230880629 4738341969856778927895059)
                  ·
                    refine ⟨7107512954785168391842589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4738341969856778927895059 7107512954785168391842589)
                    ·
                      refine ⟨2665317358044438146940971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7107512954785168391842589 2665317358044438146940971)
                      ·
                        rfl

theorem cell23_5190687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_5190687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190687 prefixEnd_5190687 := by exact prefixLift 5190687
  have htrace : WordTrace (prefixWord ++ tailWord_5190687) baseStart_5190687 baseEnd_5190687 := by
    simpa [prefixWord, tailWord_5190687, baseEnd_5190687] using wordTrace_append hprefix tailTrace_5190687
  have hstable : (prefixWord ++ tailWord_5190687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190687).length < 2 ^ (prefixWord ++ tailWord_5190687).sum := by decide
  have hdescent : baseEnd_5190687 < baseStart_5190687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190703 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 10]
def baseStart_5190703 : Nat := 118140960795 + 5190703 * 2 ^ 59
def prefixEnd_5190703 : Nat := 4983230072969 + 3 ^ 40 * 5190703 * 2
def baseEnd_5190703 : Nat := 888441857911636694780299

theorem tailTrace_5190703 : CollatzResearch.WordTrace tailWord_5190703 prefixEnd_5190703 888441857911636694780299 := by
  unfold tailWord_5190703
  simp only [CollatzResearch.WordTrace]
  refine ⟨189320491713977007339520763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126213661142651338226347175 189320491713977007339520763)
  ·
    refine ⟨283980737570965511009281145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189320491713977007339520763 283980737570965511009281145)
    ·
      refine ⟨212985553178224133256960859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283980737570965511009281145 212985553178224133256960859)
      ·
        refine ⟨319478329767336199885441289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212985553178224133256960859 319478329767336199885441289)
        ·
          refine ⟨239608747325502149914080967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319478329767336199885441289 239608747325502149914080967)
          ·
            refine ⟨359413120988253224871121451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239608747325502149914080967 359413120988253224871121451)
            ·
              refine ⟨539119681482379837306682177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359413120988253224871121451 539119681482379837306682177)
              ·
                refine ⟨404339761111784877980011633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539119681482379837306682177 404339761111784877980011633)
                ·
                  refine ⟨303254820833838658485008725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404339761111784877980011633 303254820833838658485008725)
                  ·
                    refine ⟨888441857911636694780299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 303254820833838658485008725 888441857911636694780299)
                    ·
                      rfl

theorem cell23_5190703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_5190703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190703 prefixEnd_5190703 := by exact prefixLift 5190703
  have htrace : WordTrace (prefixWord ++ tailWord_5190703) baseStart_5190703 baseEnd_5190703 := by
    simpa [prefixWord, tailWord_5190703, baseEnd_5190703] using wordTrace_append hprefix tailTrace_5190703
  have hstable : (prefixWord ++ tailWord_5190703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190703).length < 2 ^ (prefixWord ++ tailWord_5190703).sum := by decide
  have hdescent : baseEnd_5190703 < baseStart_5190703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190721 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5190721 : Nat := 118140960795 + 5190721 * 2 ^ 59
def prefixEnd_5190721 : Nat := 4983230072969 + 3 ^ 40 * 5190721 * 2
def baseEnd_5190721 : Nat := 2665334816386691013915815

theorem tailTrace_5190721 : CollatzResearch.WordTrace tailWord_5190721 prefixEnd_5190721 2665334816386691013915815 := by
  unfold tailWord_5190721
  simp only [CollatzResearch.WordTrace]
  refine ⟨189321148227911796413676017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126214098818607864275784011 189321148227911796413676017)
  ·
    refine ⟨141990861170933847310257013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189321148227911796413676017 141990861170933847310257013)
    ·
      refine ⟨13311643234775048185336595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141990861170933847310257013 13311643234775048185336595)
      ·
        refine ⟨19967464852162572278004893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13311643234775048185336595 19967464852162572278004893)
        ·
          refine ⟨7487799319560964604251835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19967464852162572278004893 7487799319560964604251835)
          ·
            refine ⟨11231698979341446906377753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7487799319560964604251835 11231698979341446906377753)
            ·
              refine ⟨8423774234506085179783315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11231698979341446906377753 8423774234506085179783315)
              ·
                refine ⟨12635661351759127769674973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8423774234506085179783315 12635661351759127769674973)
                ·
                  refine ⟨4738373006909672913628115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12635661351759127769674973 4738373006909672913628115)
                  ·
                    refine ⟨7107559510364509370442173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4738373006909672913628115 7107559510364509370442173)
                    ·
                      refine ⟨2665334816386691013915815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7107559510364509370442173 2665334816386691013915815)
                      ·
                        rfl

theorem cell23_5190721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5190721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190721 prefixEnd_5190721 := by exact prefixLift 5190721
  have htrace : WordTrace (prefixWord ++ tailWord_5190721) baseStart_5190721 baseEnd_5190721 := by
    simpa [prefixWord, tailWord_5190721, baseEnd_5190721] using wordTrace_append hprefix tailTrace_5190721
  have hstable : (prefixWord ++ tailWord_5190721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190721).length < 2 ^ (prefixWord ++ tailWord_5190721).sum := by decide
  have hdescent : baseEnd_5190721 < baseStart_5190721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190730 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_5190730 : Nat := 118140960795 + 5190730 * 2 ^ 59
def prefixEnd_5190730 : Nat := 4983230072969 + 3 ^ 40 * 5190730 * 2
def baseEnd_5190730 : Nat := 2665339437712581478703273

theorem tailTrace_5190730 : CollatzResearch.WordTrace tailWord_5190730 prefixEnd_5190730 2665339437712581478703273 := by
  unfold tailWord_5190730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47330369121219797737688411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126214317656586127300502429 47330369121219797737688411)
  ·
    refine ⟨70995553681829696606532617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47330369121219797737688411 70995553681829696606532617)
    ·
      refine ⟨53246665261372272454899463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70995553681829696606532617 53246665261372272454899463)
      ·
        refine ⟨79869997892058408682349195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53246665261372272454899463 79869997892058408682349195)
        ·
          refine ⟨119804996838087613023523793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79869997892058408682349195 119804996838087613023523793)
          ·
            refine ⟨89853747628565709767642845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119804996838087613023523793 89853747628565709767642845)
            ·
              refine ⟨33695155360712141162866067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89853747628565709767642845 33695155360712141162866067)
              ·
                refine ⟨50542733041068211744299101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33695155360712141162866067 50542733041068211744299101)
                ·
                  refine ⟨18953524890400579404112163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50542733041068211744299101 18953524890400579404112163)
                  ·
                    refine ⟨28430287335600869106168245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18953524890400579404112163 28430287335600869106168245)
                    ·
                      refine ⟨2665339437712581478703273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28430287335600869106168245 2665339437712581478703273)
                      ·
                        rfl

theorem cell23_5190730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_5190730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190730 prefixEnd_5190730 := by exact prefixLift 5190730
  have htrace : WordTrace (prefixWord ++ tailWord_5190730) baseStart_5190730 baseEnd_5190730 := by
    simpa [prefixWord, tailWord_5190730, baseEnd_5190730] using wordTrace_append hprefix tailTrace_5190730
  have hstable : (prefixWord ++ tailWord_5190730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190730).length < 2 ^ (prefixWord ++ tailWord_5190730).sum := by decide
  have hdescent : baseEnd_5190730 < baseStart_5190730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190737 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 2, 4]
def baseStart_5190737 : Nat := 118140960795 + 5190737 * 2 ^ 59
def prefixEnd_5190737 : Nat := 4983230072969 + 3 ^ 40 * 5190737 * 2
def baseEnd_5190737 : Nat := 888447677359054317105247

theorem tailTrace_5190737 : CollatzResearch.WordTrace tailWord_5190737 prefixEnd_5190737 888447677359054317105247 := by
  unfold tailWord_5190737
  simp only [CollatzResearch.WordTrace]
  refine ⟨189321731795853831146258465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126214487863902554097505643 189321731795853831146258465)
  ·
    refine ⟨141991298846890373359693849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189321731795853831146258465 141991298846890373359693849)
    ·
      refine ⟨106493474135167780019770387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141991298846890373359693849 106493474135167780019770387)
      ·
        refine ⟨159740211202751670029655581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106493474135167780019770387 159740211202751670029655581)
        ·
          refine ⟨59902579201031876261120843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159740211202751670029655581 59902579201031876261120843)
          ·
            refine ⟨89853868801547814391681265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59902579201031876261120843 89853868801547814391681265)
            ·
              refine ⟨67390401601160860793760949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89853868801547814391681265 67390401601160860793760949)
              ·
                refine ⟨6317850150108830699415089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67390401601160860793760949 6317850150108830699415089)
                ·
                  refine ⟨4738387612581623024561317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6317850150108830699415089 4738387612581623024561317)
                  ·
                    refine ⟨888447677359054317105247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738387612581623024561317 888447677359054317105247)
                    ·
                      rfl

theorem cell23_5190737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_5190737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190737 prefixEnd_5190737 := by exact prefixLift 5190737
  have htrace : WordTrace (prefixWord ++ tailWord_5190737) baseStart_5190737 baseEnd_5190737 := by
    simpa [prefixWord, tailWord_5190737, baseEnd_5190737] using wordTrace_append hprefix tailTrace_5190737
  have hstable : (prefixWord ++ tailWord_5190737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190737).length < 2 ^ (prefixWord ++ tailWord_5190737).sum := by decide
  have hdescent : baseEnd_5190737 < baseStart_5190737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190744 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 3, 2, 2]
def baseStart_5190744 : Nat := 118140960795 + 5190744 * 2 ^ 59
def prefixEnd_5190744 : Nat := 4983230072969 + 3 ^ 40 * 5190744 * 2
def baseEnd_5190744 : Nat := 2665346626441744423928209

theorem tailTrace_5190744 : CollatzResearch.WordTrace tailWord_5190744 prefixEnd_5190744 2665346626441744423928209 := by
  unfold tailWord_5190744
  simp only [CollatzResearch.WordTrace]
  refine ⟨94660993553414235670881643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126214658071218980894508857 94660993553414235670881643)
  ·
    refine ⟨141991490330121353506322465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94660993553414235670881643 141991490330121353506322465)
    ·
      refine ⟨106493617747591015129741849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141991490330121353506322465 106493617747591015129741849)
      ·
        refine ⟨79870213310693261347306387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106493617747591015129741849 79870213310693261347306387)
        ·
          refine ⟨119805319966039892020959581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79870213310693261347306387 119805319966039892020959581)
          ·
            refine ⟨44926994987264959507859843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119805319966039892020959581 44926994987264959507859843)
            ·
              refine ⟨67390492480897439261789765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44926994987264959507859843 67390492480897439261789765)
              ·
                refine ⟨12635717340168269861585581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67390492480897439261789765 12635717340168269861585581)
                ·
                  refine ⟨4738394002563101198094593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12635717340168269861585581 4738394002563101198094593)
                  ·
                    refine ⟨3553795501922325898570945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4738394002563101198094593 3553795501922325898570945)
                    ·
                      refine ⟨2665346626441744423928209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553795501922325898570945 2665346626441744423928209)
                      ·
                        rfl

theorem cell23_5190744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_5190744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190744 prefixEnd_5190744 := by exact prefixLift 5190744
  have htrace : WordTrace (prefixWord ++ tailWord_5190744) baseStart_5190744 baseEnd_5190744 := by
    simpa [prefixWord, tailWord_5190744, baseEnd_5190744] using wordTrace_append hprefix tailTrace_5190744
  have hstable : (prefixWord ++ tailWord_5190744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190744).length < 2 ^ (prefixWord ++ tailWord_5190744).sum := by decide
  have hdescent : baseEnd_5190744 < baseStart_5190744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190754 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5190754 : Nat := 118140960795 + 5190754 * 2 ^ 59
def prefixEnd_5190754 : Nat := 4983230072969 + 3 ^ 40 * 5190754 * 2
def baseEnd_5190754 : Nat := 888450587082763128267721

theorem tailTrace_5190754 : CollatzResearch.WordTrace tailWord_5190754 prefixEnd_5190754 888450587082763128267721 := by
  unfold tailWord_5190754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47330587959198060762406829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126214901224528162033084877 47330587959198060762406829)
  ·
    refine ⟨17748970484699272785902561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47330587959198060762406829 17748970484699272785902561)
    ·
      refine ⟨13311727863524454589426921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17748970484699272785902561 13311727863524454589426921)
      ·
        refine ⟨9983795897643340942070191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13311727863524454589426921 9983795897643340942070191)
        ·
          refine ⟨14975693846465011413105287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9983795897643340942070191 14975693846465011413105287)
          ·
            refine ⟨22463540769697517119657931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14975693846465011413105287 22463540769697517119657931)
            ·
              refine ⟨33695311154546275679486897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22463540769697517119657931 33695311154546275679486897)
              ·
                refine ⟨25271483365909706759615173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33695311154546275679486897 25271483365909706759615173)
                ·
                  refine ⟨4738403131108070017427845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25271483365909706759615173 4738403131108070017427845)
                  ·
                    refine ⟨888450587082763128267721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738403131108070017427845 888450587082763128267721)
                    ·
                      rfl

theorem cell23_5190754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5190754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190754 prefixEnd_5190754 := by exact prefixLift 5190754
  have htrace : WordTrace (prefixWord ++ tailWord_5190754) baseStart_5190754 baseEnd_5190754 := by
    simpa [prefixWord, tailWord_5190754, baseEnd_5190754] using wordTrace_append hprefix tailTrace_5190754
  have hstable : (prefixWord ++ tailWord_5190754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190754).length < 2 ^ (prefixWord ++ tailWord_5190754).sum := by decide
  have hdescent : baseEnd_5190754 < baseStart_5190754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190780 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_5190780 : Nat := 118140960795 + 5190780 * 2 ^ 59
def prefixEnd_5190780 : Nat := 4983230072969 + 3 ^ 40 * 5190780 * 2
def baseEnd_5190780 : Nat := 888455037248435427692681

theorem tailTrace_5190780 : CollatzResearch.WordTrace tailWord_5190780 prefixEnd_5190780 888455037248435427692681 := by
  unfold tailWord_5190780
  simp only [CollatzResearch.WordTrace]
  refine ⟨94661650067349024745036897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126215533423132032993382529 94661650067349024745036897)
  ·
    refine ⟨70996237550511768558777673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94661650067349024745036897 70996237550511768558777673)
    ·
      refine ⟨53247178162883826419083255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70996237550511768558777673 53247178162883826419083255)
      ·
        refine ⟨79870767244325739628624883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53247178162883826419083255 79870767244325739628624883)
        ·
          refine ⟨119806150866488609442937325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79870767244325739628624883 119806150866488609442937325)
          ·
            refine ⟨44927306574933228541101497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119806150866488609442937325 44927306574933228541101497)
            ·
              refine ⟨33695479931199921405826123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44927306574933228541101497 33695479931199921405826123)
              ·
                refine ⟨50543219896799882108739185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33695479931199921405826123 50543219896799882108739185)
                ·
                  refine ⟨37907414922599911581554389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50543219896799882108739185 37907414922599911581554389)
                  ·
                    refine ⟨888455037248435427692681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37907414922599911581554389 888455037248435427692681)
                    ·
                      rfl

theorem cell23_5190780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_5190780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190780 prefixEnd_5190780 := by exact prefixLift 5190780
  have htrace : WordTrace (prefixWord ++ tailWord_5190780) baseStart_5190780 baseEnd_5190780 := by
    simpa [prefixWord, tailWord_5190780, baseEnd_5190780] using wordTrace_append hprefix tailTrace_5190780
  have hstable : (prefixWord ++ tailWord_5190780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190780).length < 2 ^ (prefixWord ++ tailWord_5190780).sum := by decide
  have hdescent : baseEnd_5190780 < baseStart_5190780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190800 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_5190800 : Nat := 118140960795 + 5190800 * 2 ^ 59
def prefixEnd_5190800 : Nat := 4983230072969 + 3 ^ 40 * 5190800 * 2
def baseEnd_5190800 : Nat := 2665375381358396204827951

theorem tailTrace_5190800 : CollatzResearch.WordTrace tailWord_5190800 prefixEnd_5190800 2665375381358396204827951 := by
  unfold tailWord_5190800
  simp only [CollatzResearch.WordTrace]
  refine ⟨94662014797312796452900927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126216019729750395270534569 94662014797312796452900927)
  ·
    refine ⟨141993022195969194679351391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94662014797312796452900927 141993022195969194679351391)
    ·
      refine ⟨212989533293953792019027087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141993022195969194679351391 212989533293953792019027087)
      ·
        refine ⟨319484299940930688028540631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212989533293953792019027087 319484299940930688028540631)
        ·
          refine ⟨479226449911396032042810947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319484299940930688028540631 479226449911396032042810947)
          ·
            refine ⟨718839674867094048064216421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479226449911396032042810947 718839674867094048064216421)
            ·
              refine ⟨134782439037580134012040579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 718839674867094048064216421 134782439037580134012040579)
              ·
                refine ⟨202173658556370201018060869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134782439037580134012040579 202173658556370201018060869)
                ·
                  refine ⟨37907560979319412690886413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202173658556370201018060869 37907560979319412690886413)
                  ·
                    refine ⟨14215335367244779759082405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37907560979319412690886413 14215335367244779759082405)
                    ·
                      refine ⟨2665375381358396204827951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14215335367244779759082405 2665375381358396204827951)
                      ·
                        rfl

theorem cell23_5190800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_5190800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190800 prefixEnd_5190800 := by exact prefixLift 5190800
  have htrace : WordTrace (prefixWord ++ tailWord_5190800) baseStart_5190800 baseEnd_5190800 := by
    simpa [prefixWord, tailWord_5190800, baseEnd_5190800] using wordTrace_append hprefix tailTrace_5190800
  have hstable : (prefixWord ++ tailWord_5190800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190800).length < 2 ^ (prefixWord ++ tailWord_5190800).sum := by decide
  have hdescent : baseEnd_5190800 < baseStart_5190800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190829 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_5190829 : Nat := 118140960795 + 5190829 * 2 ^ 59
def prefixEnd_5190829 : Nat := 4983230072969 + 3 ^ 40 * 5190829 * 2
def baseEnd_5190829 : Nat := 2665390272297376591365319

theorem tailTrace_5190829 : CollatzResearch.WordTrace tailWord_5190829 prefixEnd_5190829 2665390272297376591365319 := by
  unfold tailWord_5190829
  simp only [CollatzResearch.WordTrace]
  refine ⟨189325087311520530858607541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126216724874347020572405027 189325087311520530858607541)
  ·
    refine ⟨17749226935455049767994457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189325087311520530858607541 17749226935455049767994457)
    ·
      refine ⟨13311920201591287325995843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17749226935455049767994457 13311920201591287325995843)
      ·
        refine ⟨19967880302386930988993765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13311920201591287325995843 19967880302386930988993765)
        ·
          refine ⟨3743977556697549560436331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19967880302386930988993765 3743977556697549560436331)
          ·
            refine ⟨5615966335046324340654497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743977556697549560436331 5615966335046324340654497)
            ·
              refine ⟨4211974751284743255490873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5615966335046324340654497 4211974751284743255490873)
              ·
                refine ⟨3158981063463557441618155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211974751284743255490873 3158981063463557441618155)
                ·
                  refine ⟨4738471595195336162427233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158981063463557441618155 4738471595195336162427233)
                  ·
                    refine ⟨3553853696396502121820425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4738471595195336162427233 3553853696396502121820425)
                    ·
                      refine ⟨2665390272297376591365319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553853696396502121820425 2665390272297376591365319)
                      ·
                        rfl

theorem cell23_5190829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_5190829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190829 prefixEnd_5190829 := by exact prefixLift 5190829
  have htrace : WordTrace (prefixWord ++ tailWord_5190829) baseStart_5190829 baseEnd_5190829 := by
    simpa [prefixWord, tailWord_5190829, baseEnd_5190829] using wordTrace_append hprefix tailTrace_5190829
  have hstable : (prefixWord ++ tailWord_5190829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190829).length < 2 ^ (prefixWord ++ tailWord_5190829).sum := by decide
  have hdescent : baseEnd_5190829 < baseStart_5190829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190885 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 2, 2, 2]
def baseStart_5190885 : Nat := 118140960795 + 5190885 * 2 ^ 59
def prefixEnd_5190885 : Nat := 4983230072969 + 3 ^ 40 * 5190885 * 2
def baseEnd_5190885 : Nat := 2665419027214028372265061

theorem tailTrace_5190885 : CollatzResearch.WordTrace tailWord_5190885 prefixEnd_5190885 2665419027214028372265061 := by
  unfold tailWord_5190885
  simp only [CollatzResearch.WordTrace]
  refine ⟨189327129799317652422646109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126218086532878434948430739 189327129799317652422646109)
  ·
    refine ⟨70997673674744119658492291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189327129799317652422646109 70997673674744119658492291)
    ·
      refine ⟨106496510512116179487738437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70997673674744119658492291 106496510512116179487738437)
      ·
        refine ⟨19968095721021783653950957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106496510512116179487738437 19968095721021783653950957)
        ·
          refine ⟨7488035895383168870231609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19968095721021783653950957 7488035895383168870231609)
          ·
            refine ⟨5616026921537376652673707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7488035895383168870231609 5616026921537376652673707)
            ·
              refine ⟨8424040382306064979010561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5616026921537376652673707 8424040382306064979010561)
              ·
                refine ⟨6318030286729548734257921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8424040382306064979010561 6318030286729548734257921)
                ·
                  refine ⟨4738522715047161550693441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6318030286729548734257921 4738522715047161550693441)
                  ·
                    refine ⟨3553892036285371163020081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4738522715047161550693441 3553892036285371163020081)
                    ·
                      refine ⟨2665419027214028372265061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553892036285371163020081 2665419027214028372265061)
                      ·
                        rfl

theorem cell23_5190885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_5190885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190885 prefixEnd_5190885 := by exact prefixLift 5190885
  have htrace : WordTrace (prefixWord ++ tailWord_5190885) baseStart_5190885 baseEnd_5190885 := by
    simpa [prefixWord, tailWord_5190885, baseEnd_5190885] using wordTrace_append hprefix tailTrace_5190885
  have hstable : (prefixWord ++ tailWord_5190885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190885).length < 2 ^ (prefixWord ++ tailWord_5190885).sum := by decide
  have hdescent : baseEnd_5190885 < baseStart_5190885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190894 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_5190894 : Nat := 118140960795 + 5190894 * 2 ^ 59
def prefixEnd_5190894 : Nat := 4983230072969 + 3 ^ 40 * 5190894 * 2
def baseEnd_5190894 : Nat := 2665423648539918837052519

theorem tailTrace_5190894 : CollatzResearch.WordTrace tailWord_5190894 prefixEnd_5190894 2665423648539918837052519 := by
  unfold tailWord_5190894
  simp only [CollatzResearch.WordTrace]
  refine ⟨23665932257035630869965467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126218305370856697973149157 23665932257035630869965467)
  ·
    refine ⟨35498898385553446304948201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23665932257035630869965467 35498898385553446304948201)
    ·
      refine ⟨26624173789165084728711151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35498898385553446304948201 26624173789165084728711151)
      ·
        refine ⟨39936260683747627093066727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26624173789165084728711151 39936260683747627093066727)
        ·
          refine ⟨59904391025621440639600091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39936260683747627093066727 59904391025621440639600091)
          ·
            refine ⟨89856586538432160959400137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59904391025621440639600091 89856586538432160959400137)
            ·
              refine ⟨67392439903824120719550103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89856586538432160959400137 67392439903824120719550103)
              ·
                refine ⟨101088659855736181079325155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67392439903824120719550103 101088659855736181079325155)
                ·
                  refine ⟨151632989783604271618987733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101088659855736181079325155 151632989783604271618987733)
                  ·
                    refine ⟨3553898198053225116070025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151632989783604271618987733 3553898198053225116070025)
                    ·
                      refine ⟨2665423648539918837052519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553898198053225116070025 2665423648539918837052519)
                      ·
                        rfl

theorem cell23_5190894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_5190894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190894 prefixEnd_5190894 := by exact prefixLift 5190894
  have htrace : WordTrace (prefixWord ++ tailWord_5190894) baseStart_5190894 baseEnd_5190894 := by
    simpa [prefixWord, tailWord_5190894, baseEnd_5190894] using wordTrace_append hprefix tailTrace_5190894
  have hstable : (prefixWord ++ tailWord_5190894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190894).length < 2 ^ (prefixWord ++ tailWord_5190894).sum := by decide
  have hdescent : baseEnd_5190894 < baseStart_5190894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190941 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5190941 : Nat := 118140960795 + 5190941 * 2 ^ 59
def prefixEnd_5190941 : Nat := 4983230072969 + 3 ^ 40 * 5190941 * 2
def baseEnd_5190941 : Nat := 2665447782130680153164803

theorem tailTrace_5190941 : CollatzResearch.WordTrace tailWord_5190941 prefixEnd_5190941 2665447782130680153164803 := by
  unfold tailWord_5190941
  simp only [CollatzResearch.WordTrace]
  refine ⟨189329172287114773986684677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126219448191409849324456451 189329172287114773986684677)
  ·
    refine ⟨35499219803834020122503377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189329172287114773986684677 35499219803834020122503377)
    ·
      refine ⟨26624414852875515091877533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35499219803834020122503377 26624414852875515091877533)
      ·
        refine ⟨9984155569828318159454075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26624414852875515091877533 9984155569828318159454075)
        ·
          refine ⟨14976233354742477239181113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9984155569828318159454075 14976233354742477239181113)
          ·
            refine ⟨11232175016056857929385835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14976233354742477239181113 11232175016056857929385835)
            ·
              refine ⟨16848262524085286894078753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11232175016056857929385835 16848262524085286894078753)
              ·
                refine ⟨12636196893063965170559065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16848262524085286894078753 12636196893063965170559065)
                ·
                  refine ⟨9477147669797973877919299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12636196893063965170559065 9477147669797973877919299)
                  ·
                    refine ⟨14215721504696960816878949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9477147669797973877919299 14215721504696960816878949)
                    ·
                      refine ⟨2665447782130680153164803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14215721504696960816878949 2665447782130680153164803)
                      ·
                        rfl

theorem cell23_5190941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5190941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190941 prefixEnd_5190941 := by exact prefixLift 5190941
  have htrace : WordTrace (prefixWord ++ tailWord_5190941) baseStart_5190941 baseEnd_5190941 := by
    simpa [prefixWord, tailWord_5190941, baseEnd_5190941] using wordTrace_append hprefix tailTrace_5190941
  have hstable : (prefixWord ++ tailWord_5190941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190941).length < 2 ^ (prefixWord ++ tailWord_5190941).sum := by decide
  have hdescent : baseEnd_5190941 < baseStart_5190941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5190947 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 8]
def baseStart_5190947 : Nat := 118140960795 + 5190947 * 2 ^ 59
def prefixEnd_5190947 : Nat := 4983230072969 + 3 ^ 40 * 5190947 * 2
def baseEnd_5190947 : Nat := 296161207001623014409975

theorem tailTrace_5190947 : CollatzResearch.WordTrace tailWord_5190947 prefixEnd_5190947 296161207001623014409975 := by
  unfold tailWord_5190947
  simp only [CollatzResearch.WordTrace]
  refine ⟨189329391125093037011403095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126219594083395358007602063 189329391125093037011403095)
  ·
    refine ⟨283994086687639555517104643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189329391125093037011403095 283994086687639555517104643)
    ·
      refine ⟨425991130031459333275656965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283994086687639555517104643 425991130031459333275656965)
      ·
        refine ⟨79873336880898624989185681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425991130031459333275656965 79873336880898624989185681)
        ·
          refine ⟨59905002660673968741889261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79873336880898624989185681 59905002660673968741889261)
          ·
            refine ⟨22464375997752738278208473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59905002660673968741889261 22464375997752738278208473)
            ·
              refine ⟨16848281998314553708656355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22464375997752738278208473 16848281998314553708656355)
              ·
                refine ⟨25272422997471830562984533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16848281998314553708656355 25272422997471830562984533)
                ·
                  refine ⟨296161207001623014409975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25272422997471830562984533 296161207001623014409975)
                  ·
                    rfl

theorem cell23_5190947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 8].length) (baseStart_5190947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5190947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5190947 prefixEnd_5190947 := by exact prefixLift 5190947
  have htrace : WordTrace (prefixWord ++ tailWord_5190947) baseStart_5190947 baseEnd_5190947 := by
    simpa [prefixWord, tailWord_5190947, baseEnd_5190947] using wordTrace_append hprefix tailTrace_5190947
  have hstable : (prefixWord ++ tailWord_5190947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5190947).length < 2 ^ (prefixWord ++ tailWord_5190947).sum := by decide
  have hdescent : baseEnd_5190947 < baseStart_5190947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5190947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191001 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 2, 3, 2]
def baseStart_5191001 : Nat := 118140960795 + 5191001 * 2 ^ 59
def prefixEnd_5191001 : Nat := 4983230072969 + 3 ^ 40 * 5191001 * 2
def baseEnd_5191001 : Nat := 2665478590969949918414527

theorem tailTrace_5191001 : CollatzResearch.WordTrace tailWord_5191001 prefixEnd_5191001 2665478590969949918414527 := by
  unfold tailWord_5191001
  simp only [CollatzResearch.WordTrace]
  refine ⟨189331360666897404233868857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126220907111264936155912571 189331360666897404233868857)
  ·
    refine ⟨141998520500173053175401643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189331360666897404233868857 141998520500173053175401643)
    ·
      refine ⟨212997780750259579763102465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141998520500173053175401643 212997780750259579763102465)
      ·
        refine ⟨159748335562694684822326849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212997780750259579763102465 159748335562694684822326849)
        ·
          refine ⟨119811251672021013616745137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159748335562694684822326849 119811251672021013616745137)
          ·
            refine ⟨89858438754015760212558853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119811251672021013616745137 89858438754015760212558853)
            ·
              refine ⟨16848457266377955039854785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89858438754015760212558853 16848457266377955039854785)
              ·
                refine ⟨12636342949783466279891089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16848457266377955039854785 12636342949783466279891089)
                ·
                  refine ⟨9477257212337599709918317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12636342949783466279891089 9477257212337599709918317)
                  ·
                    refine ⟨3553971454626599891219369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9477257212337599709918317 3553971454626599891219369)
                    ·
                      refine ⟨2665478590969949918414527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553971454626599891219369 2665478590969949918414527)
                      ·
                        rfl

theorem cell23_5191001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_5191001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191001 prefixEnd_5191001 := by exact prefixLift 5191001
  have htrace : WordTrace (prefixWord ++ tailWord_5191001) baseStart_5191001 baseEnd_5191001 := by
    simpa [prefixWord, tailWord_5191001, baseEnd_5191001] using wordTrace_append hprefix tailTrace_5191001
  have hstable : (prefixWord ++ tailWord_5191001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191001).length < 2 ^ (prefixWord ++ tailWord_5191001).sum := by decide
  have hdescent : baseEnd_5191001 < baseStart_5191001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191007 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 5, 6]
def baseStart_5191007 : Nat := 118140960795 + 5191007 * 2 ^ 59
def prefixEnd_5191007 : Nat := 4983230072969 + 3 ^ 40 * 5191007 * 2
def baseEnd_5191007 : Nat := 888493890617958964979833

theorem tailTrace_5191007 : CollatzResearch.WordTrace tailWord_5191007 prefixEnd_5191007 888493890617958964979833 := by
  unfold tailWord_5191007
  simp only [CollatzResearch.WordTrace]
  refine ⟨189331579504875667258587275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126221053003250444839058183 189331579504875667258587275)
  ·
    refine ⟨283997369257313500887880913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189331579504875667258587275 283997369257313500887880913)
    ·
      refine ⟨212998026942985125665910685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283997369257313500887880913 212998026942985125665910685)
      ·
        refine ⟨79874260103619422124716507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212998026942985125665910685 79874260103619422124716507)
        ·
          refine ⟨119811390155429133187074761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79874260103619422124716507 119811390155429133187074761)
          ·
            refine ⟨89858542616571849890306071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119811390155429133187074761 89858542616571849890306071)
            ·
              refine ⟨134787813924857774835459107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89858542616571849890306071 134787813924857774835459107)
              ·
                refine ⟨202181720887286662253188661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134787813924857774835459107 202181720887286662253188661)
                ·
                  refine ⟨18954536333183124586236437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202181720887286662253188661 18954536333183124586236437)
                  ·
                    refine ⟨888493890617958964979833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18954536333183124586236437 888493890617958964979833)
                    ·
                      rfl

theorem cell23_5191007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_5191007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191007 prefixEnd_5191007 := by exact prefixLift 5191007
  have htrace : WordTrace (prefixWord ++ tailWord_5191007) baseStart_5191007 baseEnd_5191007 := by
    simpa [prefixWord, tailWord_5191007, baseEnd_5191007] using wordTrace_append hprefix tailTrace_5191007
  have hstable : (prefixWord ++ tailWord_5191007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191007).length < 2 ^ (prefixWord ++ tailWord_5191007).sum := by decide
  have hdescent : baseEnd_5191007 < baseStart_5191007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191024 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 1, 6]
def baseStart_5191024 : Nat := 118140960795 + 5191024 * 2 ^ 59
def prefixEnd_5191024 : Nat := 4983230072969 + 3 ^ 40 * 5191024 * 2
def baseEnd_5191024 : Nat := 888496800341667776142307

theorem tailTrace_5191024 : CollatzResearch.WordTrace tailWord_5191024 prefixEnd_5191024 888496800341667776142307 := by
  unfold tailWord_5191024
  simp only [CollatzResearch.WordTrace]
  refine ⟨94666099772907039580978063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126221466363876052774637417 94666099772907039580978063)
  ·
    refine ⟨141999149659360559371467095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94666099772907039580978063 141999149659360559371467095)
    ·
      refine ⟨212998724489040839057200643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141999149659360559371467095 212998724489040839057200643)
      ·
        refine ⟨319498086733561258585800965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212998724489040839057200643 319498086733561258585800965)
        ·
          refine ⟨59905891262542735984837681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319498086733561258585800965 59905891262542735984837681)
          ·
            refine ⟨44929418446907051988628261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59905891262542735984837681 44929418446907051988628261)
            ·
              refine ⟨8424265958795072247867799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44929418446907051988628261 8424265958795072247867799)
              ·
                refine ⟨12636398938192608371801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8424265958795072247867799 12636398938192608371801699)
                ·
                  refine ⟨18954598407288912557702549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12636398938192608371801699 18954598407288912557702549)
                  ·
                    refine ⟨888496800341667776142307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18954598407288912557702549 888496800341667776142307)
                    ·
                      rfl

theorem cell23_5191024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_5191024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191024 prefixEnd_5191024 := by exact prefixLift 5191024
  have htrace : WordTrace (prefixWord ++ tailWord_5191024) baseStart_5191024 baseEnd_5191024 := by
    simpa [prefixWord, tailWord_5191024, baseEnd_5191024] using wordTrace_append hprefix tailTrace_5191024
  have hstable : (prefixWord ++ tailWord_5191024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191024).length < 2 ^ (prefixWord ++ tailWord_5191024).sum := by decide
  have hdescent : baseEnd_5191024 < baseStart_5191024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191042 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5191042 : Nat := 118140960795 + 5191042 * 2 ^ 59
def prefixEnd_5191042 : Nat := 4983230072969 + 3 ^ 40 * 5191042 * 2
def baseEnd_5191042 : Nat := 2665499643676784258001839

theorem tailTrace_5191042 : CollatzResearch.WordTrace tailWord_5191042 prefixEnd_5191042 2665499643676784258001839 := by
  unfold tailWord_5191042
  simp only [CollatzResearch.WordTrace]
  refine ⟨47333214014937217059027845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126221904039832578824074253 47333214014937217059027845)
  ·
    refine ⟨8874977627800728198567721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47333214014937217059027845 8874977627800728198567721)
    ·
      refine ⟨6656233220850546148925791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8874977627800728198567721 6656233220850546148925791)
      ·
        refine ⟨9984349831275819223388687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6656233220850546148925791 9984349831275819223388687)
        ·
          refine ⟨14976524746913728835083031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9984349831275819223388687 14976524746913728835083031)
          ·
            refine ⟨22464787120370593252624547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14976524746913728835083031 22464787120370593252624547)
            ·
              refine ⟨33697180680555889878936821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22464787120370593252624547 33697180680555889878936821)
              ·
                refine ⟨3159110688802114676150327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33697180680555889878936821 3159110688802114676150327)
                ·
                  refine ⟨4738666033203172014225491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159110688802114676150327 4738666033203172014225491)
                  ·
                    refine ⟨7107999049804758021338237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4738666033203172014225491 7107999049804758021338237)
                    ·
                      refine ⟨2665499643676784258001839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7107999049804758021338237 2665499643676784258001839)
                      ·
                        rfl

theorem cell23_5191042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5191042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191042 prefixEnd_5191042 := by exact prefixLift 5191042
  have htrace : WordTrace (prefixWord ++ tailWord_5191042) baseStart_5191042 baseEnd_5191042 := by
    simpa [prefixWord, tailWord_5191042, baseEnd_5191042] using wordTrace_append hprefix tailTrace_5191042
  have hstable : (prefixWord ++ tailWord_5191042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191042).length < 2 ^ (prefixWord ++ tailWord_5191042).sum := by decide
  have hdescent : baseEnd_5191042 < baseStart_5191042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191048 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_5191048 : Nat := 118140960795 + 5191048 * 2 ^ 59
def prefixEnd_5191048 : Nat := 4983230072969 + 3 ^ 40 * 5191048 * 2
def baseEnd_5191048 : Nat := 2665502724560711234526811

theorem tailTrace_5191048 : CollatzResearch.WordTrace tailWord_5191048 prefixEnd_5191048 2665502724560711234526811 := by
  unfold tailWord_5191048
  simp only [CollatzResearch.WordTrace]
  refine ⟨94666537448863565630414899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126222049931818087507219865 94666537448863565630414899)
  ·
    refine ⟨141999806173295348445622349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94666537448863565630414899 141999806173295348445622349)
    ·
      refine ⟨53249927314985755667108381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141999806173295348445622349 53249927314985755667108381)
      ·
        refine ⟨19968722743119658375165643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53249927314985755667108381 19968722743119658375165643)
        ·
          refine ⟨29953084114679487562748465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19968722743119658375165643 29953084114679487562748465)
          ·
            refine ⟨22464813086009615672061349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29953084114679487562748465 22464813086009615672061349)
            ·
              refine ⟨4212152453626802938511503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22464813086009615672061349 4212152453626802938511503)
              ·
                refine ⟨6318228680440204407767255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4212152453626802938511503 6318228680440204407767255)
                ·
                  refine ⟨9477343020660306611650883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6318228680440204407767255 9477343020660306611650883)
                  ·
                    refine ⟨14216014530990459917476325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9477343020660306611650883 14216014530990459917476325)
                    ·
                      refine ⟨2665502724560711234526811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14216014530990459917476325 2665502724560711234526811)
                      ·
                        rfl

theorem cell23_5191048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_5191048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191048 prefixEnd_5191048 := by exact prefixLift 5191048
  have htrace : WordTrace (prefixWord ++ tailWord_5191048) baseStart_5191048 baseEnd_5191048 := by
    simpa [prefixWord, tailWord_5191048, baseEnd_5191048] using wordTrace_append hprefix tailTrace_5191048
  have hstable : (prefixWord ++ tailWord_5191048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191048).length < 2 ^ (prefixWord ++ tailWord_5191048).sum := by decide
  have hdescent : baseEnd_5191048 < baseStart_5191048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191051 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 3]
def baseStart_5191051 : Nat := 118140960795 + 5191051 * 2 ^ 59
def prefixEnd_5191051 : Nat := 4983230072969 + 3 ^ 40 * 5191051 * 2
def baseEnd_5191051 : Nat := 2665504265002674722789297

theorem tailTrace_5191051 : CollatzResearch.WordTrace tailWord_5191051 prefixEnd_5191051 2665504265002674722789297 := by
  unfold tailWord_5191051
  simp only [CollatzResearch.WordTrace]
  refine ⟨189333184316716262773189007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126222122877810841848792671 189333184316716262773189007)
  ·
    refine ⟨283999776475074394159783511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189333184316716262773189007 283999776475074394159783511)
    ·
      refine ⟨425999664712611591239675267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283999776475074394159783511 425999664712611591239675267)
      ·
        refine ⟨638999497068917386859512901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425999664712611591239675267 638999497068917386859512901)
        ·
          refine ⟨119812405700422010036158669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 638999497068917386859512901 119812405700422010036158669)
          ·
            refine ⟨44929652137658253763559501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119812405700422010036158669 44929652137658253763559501)
            ·
              refine ⟨16848619551621845161334813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44929652137658253763559501 16848619551621845161334813)
              ·
                refine ⟨6318232331858191935500555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16848619551621845161334813 6318232331858191935500555)
                ·
                  refine ⟨9477348497787287903250833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6318232331858191935500555 9477348497787287903250833)
                  ·
                    refine ⟨7108011373340465927438125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9477348497787287903250833 7108011373340465927438125)
                    ·
                      refine ⟨2665504265002674722789297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7108011373340465927438125 2665504265002674722789297)
                      ·
                        rfl

theorem cell23_5191051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 3].length) (baseStart_5191051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191051 prefixEnd_5191051 := by exact prefixLift 5191051
  have htrace : WordTrace (prefixWord ++ tailWord_5191051) baseStart_5191051 baseEnd_5191051 := by
    simpa [prefixWord, tailWord_5191051, baseEnd_5191051] using wordTrace_append hprefix tailTrace_5191051
  have hstable : (prefixWord ++ tailWord_5191051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191051).length < 2 ^ (prefixWord ++ tailWord_5191051).sum := by decide
  have hdescent : baseEnd_5191051 < baseStart_5191051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191065 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 1, 2, 2]
def baseStart_5191065 : Nat := 118140960795 + 5191065 * 2 ^ 59
def prefixEnd_5191065 : Nat := 4983230072969 + 3 ^ 40 * 5191065 * 2
def baseEnd_5191065 : Nat := 2665511453731837668014233

theorem tailTrace_5191065 : CollatzResearch.WordTrace tailWord_5191065 prefixEnd_5191065 2665511453731837668014233 := by
  unfold tailWord_5191065
  simp only [CollatzResearch.WordTrace]
  refine ⟨189333694938665543164198649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126222463292443695442799099 189333694938665543164198649)
  ·
    refine ⟨142000271203999157373148987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189333694938665543164198649 142000271203999157373148987)
    ·
      refine ⟨213000406805998736059723481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142000271203999157373148987 213000406805998736059723481)
      ·
        refine ⟨159750305104499052044792611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213000406805998736059723481 159750305104499052044792611)
        ·
          refine ⟨239625457656748578067188917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159750305104499052044792611 239625457656748578067188917)
          ·
            refine ⟨22464886655320179193798961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239625457656748578067188917 22464886655320179193798961)
            ·
              refine ⟨16848664991490134395349221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22464886655320179193798961 16848664991490134395349221)
              ·
                refine ⟨3159124685904400199127979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16848664991490134395349221 3159124685904400199127979)
                ·
                  refine ⟨4738687028856600298691969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159124685904400199127979 4738687028856600298691969)
                  ·
                    refine ⟨3554015271642450224018977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4738687028856600298691969 3554015271642450224018977)
                    ·
                      refine ⟨2665511453731837668014233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554015271642450224018977 2665511453731837668014233)
                      ·
                        rfl

theorem cell23_5191065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_5191065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191065 prefixEnd_5191065 := by exact prefixLift 5191065
  have htrace : WordTrace (prefixWord ++ tailWord_5191065) baseStart_5191065 baseEnd_5191065 := by
    simpa [prefixWord, tailWord_5191065, baseEnd_5191065] using wordTrace_append hprefix tailTrace_5191065
  have hstable : (prefixWord ++ tailWord_5191065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191065).length < 2 ^ (prefixWord ++ tailWord_5191065).sum := by decide
  have hdescent : baseEnd_5191065 < baseStart_5191065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191068 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5191068 : Nat := 118140960795 + 5191068 * 2 ^ 59
def prefixEnd_5191068 : Nat := 4983230072969 + 3 ^ 40 * 5191068 * 2
def baseEnd_5191068 : Nat := 2665512994173801156276719

theorem tailTrace_5191068 : CollatzResearch.WordTrace tailWord_5191068 prefixEnd_5191068 2665512994173801156276719 := by
  unfold tailWord_5191068
  simp only [CollatzResearch.WordTrace]
  refine ⟨94666902178827337338278929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126222536238436449784371905 94666902178827337338278929)
  ·
    refine ⟨71000176634120503003709197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94666902178827337338278929 71000176634120503003709197)
    ·
      refine ⟨26625066237795188626390949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71000176634120503003709197 26625066237795188626390949)
      ·
        refine ⟨4992199919586597867448303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26625066237795188626390949 4992199919586597867448303)
        ·
          refine ⟨7488299879379896801172455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992199919586597867448303 7488299879379896801172455)
          ·
            refine ⟨11232449819069845201758683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7488299879379896801172455 11232449819069845201758683)
            ·
              refine ⟨16848674728604767802638025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11232449819069845201758683 16848674728604767802638025)
              ·
                refine ⟨12636506046453575851978519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16848674728604767802638025 12636506046453575851978519)
                ·
                  refine ⟨18954759069680363777967779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12636506046453575851978519 18954759069680363777967779)
                  ·
                    refine ⟨28432138604520545666951669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18954759069680363777967779 28432138604520545666951669)
                    ·
                      refine ⟨2665512994173801156276719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28432138604520545666951669 2665512994173801156276719)
                      ·
                        rfl

theorem cell23_5191068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5191068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191068 prefixEnd_5191068 := by exact prefixLift 5191068
  have htrace : WordTrace (prefixWord ++ tailWord_5191068) baseStart_5191068 baseEnd_5191068 := by
    simpa [prefixWord, tailWord_5191068, baseEnd_5191068] using wordTrace_append hprefix tailTrace_5191068
  have hstable : (prefixWord ++ tailWord_5191068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191068).length < 2 ^ (prefixWord ++ tailWord_5191068).sum := by decide
  have hdescent : baseEnd_5191068 < baseStart_5191068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191085 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5191085 : Nat := 118140960795 + 5191085 * 2 ^ 59
def prefixEnd_5191085 : Nat := 4983230072969 + 3 ^ 40 * 5191085 * 2
def baseEnd_5191085 : Nat := 2665521723344927589764141

theorem tailTrace_5191085 : CollatzResearch.WordTrace tailWord_5191085 prefixEnd_5191085 2665521723344927589764141 := by
  unfold tailWord_5191085
  simp only [CollatzResearch.WordTrace]
  refine ⟨189334424398593086579926709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126222949599062057719951139 189334424398593086579926709)
  ·
    refine ⟨17750102287368101866868129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189334424398593086579926709 17750102287368101866868129)
    ·
      refine ⟨13312576715526076400151097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17750102287368101866868129 13312576715526076400151097)
      ·
        refine ⟨9984432536644557300113323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13312576715526076400151097 9984432536644557300113323)
        ·
          refine ⟨14976648804966835950169985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9984432536644557300113323 14976648804966835950169985)
          ·
            refine ⟨11232486603725126962627489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14976648804966835950169985 11232486603725126962627489)
            ·
              refine ⟨8424364952793845221970617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11232486603725126962627489 8424364952793845221970617)
              ·
                refine ⟨6318273714595383916477963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8424364952793845221970617 6318273714595383916477963)
                ·
                  refine ⟨9477410571893075874716945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6318273714595383916477963 9477410571893075874716945)
                  ·
                    refine ⟨7108057928919806906037709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9477410571893075874716945 7108057928919806906037709)
                    ·
                      refine ⟨2665521723344927589764141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7108057928919806906037709 2665521723344927589764141)
                      ·
                        rfl

theorem cell23_5191085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5191085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191085 prefixEnd_5191085 := by exact prefixLift 5191085
  have htrace : WordTrace (prefixWord ++ tailWord_5191085) baseStart_5191085 baseEnd_5191085 := by
    simpa [prefixWord, tailWord_5191085, baseEnd_5191085] using wordTrace_append hprefix tailTrace_5191085
  have hstable : (prefixWord ++ tailWord_5191085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191085).length < 2 ^ (prefixWord ++ tailWord_5191085).sum := by decide
  have hdescent : baseEnd_5191085 < baseStart_5191085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191091 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 3, 3, 2]
def baseStart_5191091 : Nat := 118140960795 + 5191091 * 2 ^ 59
def prefixEnd_5191091 : Nat := 4983230072969 + 3 ^ 40 * 5191091 * 2
def baseEnd_5191091 : Nat := 2665524804228854566289113

theorem tailTrace_5191091 : CollatzResearch.WordTrace tailWord_5191091 prefixEnd_5191091 2665524804228854566289113 := by
  unfold tailWord_5191091
  simp only [CollatzResearch.WordTrace]
  refine ⟨189334643236571349604645127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126223095491047566403096751 189334643236571349604645127)
  ·
    refine ⟨284001964854857024406967691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189334643236571349604645127 284001964854857024406967691)
    ·
      refine ⟨426002947282285536610451537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284001964854857024406967691 426002947282285536610451537)
      ·
        refine ⟨319502210461714152457838653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426002947282285536610451537 319502210461714152457838653)
        ·
          refine ⟨119813328923142807171689495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319502210461714152457838653 119813328923142807171689495)
          ·
            refine ⟨179719993384714210757534243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119813328923142807171689495 179719993384714210757534243)
            ·
              refine ⟨269579990077071316136301365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179719993384714210757534243 269579990077071316136301365)
              ·
                refine ⟨25273124069725435887778253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269579990077071316136301365 25273124069725435887778253)
                ·
                  refine ⟨9477421526147038457916845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25273124069725435887778253 9477421526147038457916845)
                  ·
                    refine ⟨3554033072305139421718817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9477421526147038457916845 3554033072305139421718817)
                    ·
                      refine ⟨2665524804228854566289113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554033072305139421718817 2665524804228854566289113)
                      ·
                        rfl

theorem cell23_5191091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 3, 2].length) (baseStart_5191091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191091 prefixEnd_5191091 := by exact prefixLift 5191091
  have htrace : WordTrace (prefixWord ++ tailWord_5191091) baseStart_5191091 baseEnd_5191091 := by
    simpa [prefixWord, tailWord_5191091, baseEnd_5191091] using wordTrace_append hprefix tailTrace_5191091
  have hstable : (prefixWord ++ tailWord_5191091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191091).length < 2 ^ (prefixWord ++ tailWord_5191091).sum := by decide
  have hdescent : baseEnd_5191091 < baseStart_5191091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191141 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5191141 : Nat := 118140960795 + 5191141 * 2 ^ 59
def prefixEnd_5191141 : Nat := 4983230072969 + 3 ^ 40 * 5191141 * 2
def baseEnd_5191141 : Nat := 2665550478261579370663883

theorem tailTrace_5191141 : CollatzResearch.WordTrace tailWord_5191141 prefixEnd_5191141 2665550478261579370663883 := by
  unfold tailWord_5191141
  simp only [CollatzResearch.WordTrace]
  refine ⟨189336466886390208143965277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126224311257593472095976851 189336466886390208143965277)
  ·
    refine ⟨71001175082396328053986979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189336466886390208143965277 71001175082396328053986979)
    ·
      refine ⟨106501762623594492080980469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71001175082396328053986979 106501762623594492080980469)
      ·
        refine ⟨9984540245961983632591919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106501762623594492080980469 9984540245961983632591919)
        ·
          refine ⟨14976810368942975448887879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9984540245961983632591919 14976810368942975448887879)
          ·
            refine ⟨22465215553414463173331819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14976810368942975448887879 22465215553414463173331819)
            ·
              refine ⟨33697823330121694759997729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22465215553414463173331819 33697823330121694759997729)
              ·
                refine ⟨25273367497591271069998297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33697823330121694759997729 25273367497591271069998297)
                ·
                  refine ⟨18955025623193453302498723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25273367497591271069998297 18955025623193453302498723)
                  ·
                    refine ⟨28432538434790179953748085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18955025623193453302498723 28432538434790179953748085)
                    ·
                      refine ⟨2665550478261579370663883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28432538434790179953748085 2665550478261579370663883)
                      ·
                        rfl

theorem cell23_5191141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5191141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191141 prefixEnd_5191141 := by exact prefixLift 5191141
  have htrace : WordTrace (prefixWord ++ tailWord_5191141) baseStart_5191141 baseEnd_5191141 := by
    simpa [prefixWord, tailWord_5191141, baseEnd_5191141] using wordTrace_append hprefix tailTrace_5191141
  have hstable : (prefixWord ++ tailWord_5191141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191141).length < 2 ^ (prefixWord ++ tailWord_5191141).sum := by decide
  have hdescent : baseEnd_5191141 < baseStart_5191141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191144 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 9]
def baseStart_5191144 : Nat := 118140960795 + 5191144 * 2 ^ 59
def prefixEnd_5191144 : Nat := 4983230072969 + 3 ^ 40 * 5191144 * 2
def baseEnd_5191144 : Nat := 296172446522615873214041

theorem tailTrace_5191144 : CollatzResearch.WordTrace tailWord_5191144 prefixEnd_5191144 296172446522615873214041 := by
  unfold tailWord_5191144
  simp only [CollatzResearch.WordTrace]
  refine ⟨94668288152689669828162243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126224384203586226437549657 94668288152689669828162243)
  ·
    refine ⟨142002432229034504742243365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94668288152689669828162243 142002432229034504742243365)
    ·
      refine ⟨26625456042943969639170631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142002432229034504742243365 26625456042943969639170631)
      ·
        refine ⟨39938184064415954458755947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26625456042943969639170631 39938184064415954458755947)
        ·
          refine ⟨59907276096623931688133921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39938184064415954458755947 59907276096623931688133921)
          ·
            refine ⟨44930457072467948766100441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59907276096623931688133921 44930457072467948766100441)
            ·
              refine ⟨33697842804350961574575331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44930457072467948766100441 33697842804350961574575331)
              ·
                refine ⟨50546764206526442361862997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33697842804350961574575331 50546764206526442361862997)
                ·
                  refine ⟨296172446522615873214041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50546764206526442361862997 296172446522615873214041)
                  ·
                    rfl

theorem cell23_5191144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_5191144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191144 prefixEnd_5191144 := by exact prefixLift 5191144
  have htrace : WordTrace (prefixWord ++ tailWord_5191144) baseStart_5191144 baseEnd_5191144 := by
    simpa [prefixWord, tailWord_5191144, baseEnd_5191144] using wordTrace_append hprefix tailTrace_5191144
  have hstable : (prefixWord ++ tailWord_5191144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191144).length < 2 ^ (prefixWord ++ tailWord_5191144).sum := by decide
  have hdescent : baseEnd_5191144 < baseStart_5191144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191161 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 5]
def baseStart_5191161 : Nat := 118140960795 + 5191161 * 2 ^ 59
def prefixEnd_5191161 : Nat := 4983230072969 + 3 ^ 40 * 5191161 * 2
def baseEnd_5191161 : Nat := 296173416430518810268199

theorem tailTrace_5191161 : CollatzResearch.WordTrace tailWord_5191161 prefixEnd_5191161 296173416430518810268199 := by
  unfold tailWord_5191161
  simp only [CollatzResearch.WordTrace]
  refine ⟨189337196346317751559693337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126224797564211834373128891 189337196346317751559693337)
  ·
    refine ⟨142002897259738313669770003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189337196346317751559693337 142002897259738313669770003)
    ·
      refine ⟨213004345889607470504655005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142002897259738313669770003 213004345889607470504655005)
      ·
        refine ⟨79876629708602801439245627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213004345889607470504655005 79876629708602801439245627)
        ·
          refine ⟨119814944562904202158868441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79876629708602801439245627 119814944562904202158868441)
          ·
            refine ⟨89861208422178151619151331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119814944562904202158868441 89861208422178151619151331)
            ·
              refine ⟨134791812633267227428726997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89861208422178151619151331 134791812633267227428726997)
              ·
                refine ⟨3159183108592200642860789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 134791812633267227428726997 3159183108592200642860789)
                ·
                  refine ⟨296173416430518810268199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3159183108592200642860789 296173416430518810268199)
                  ·
                    rfl

theorem cell23_5191161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 5].length) (baseStart_5191161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191161 prefixEnd_5191161 := by exact prefixLift 5191161
  have htrace : WordTrace (prefixWord ++ tailWord_5191161) baseStart_5191161 baseEnd_5191161 := by
    simpa [prefixWord, tailWord_5191161, baseEnd_5191161] using wordTrace_append hprefix tailTrace_5191161
  have hstable : (prefixWord ++ tailWord_5191161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191161).length < 2 ^ (prefixWord ++ tailWord_5191161).sum := by decide
  have hdescent : baseEnd_5191161 < baseStart_5191161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191178 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_5191178 : Nat := 118140960795 + 5191178 * 2 ^ 59
def prefixEnd_5191178 : Nat := 4983230072969 + 3 ^ 40 * 5191178 * 2
def baseEnd_5191178 : Nat := 296174386338421747322357

theorem tailTrace_5191178 : CollatzResearch.WordTrace tailWord_5191178 prefixEnd_5191178 296174386338421747322357 := by
  unfold tailWord_5191178
  simp only [CollatzResearch.WordTrace]
  refine ⟨47334454096814040865765547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126225210924837442308708125 47334454096814040865765547)
  ·
    refine ⟨71001681145221061298648321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47334454096814040865765547 71001681145221061298648321)
    ·
      refine ⟨53251260858915795973986241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71001681145221061298648321 53251260858915795973986241)
      ·
        refine ⟨39938445644186846980489681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53251260858915795973986241 39938445644186846980489681)
        ·
          refine ⟨29953834233140135235367261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39938445644186846980489681 29953834233140135235367261)
          ·
            refine ⟨11232687837427550713262723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29953834233140135235367261 11232687837427550713262723)
            ·
              refine ⟨16849031756141326069894085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11232687837427550713262723 16849031756141326069894085)
              ·
                refine ⟨3159193454276498638105141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16849031756141326069894085 3159193454276498638105141)
                ·
                  refine ⟨296174386338421747322357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3159193454276498638105141 296174386338421747322357)
                  ·
                    rfl

theorem cell23_5191178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_5191178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191178 prefixEnd_5191178 := by exact prefixLift 5191178
  have htrace : WordTrace (prefixWord ++ tailWord_5191178) baseStart_5191178 baseEnd_5191178 := by
    simpa [prefixWord, tailWord_5191178, baseEnd_5191178] using wordTrace_append hprefix tailTrace_5191178
  have hstable : (prefixWord ++ tailWord_5191178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191178).length < 2 ^ (prefixWord ++ tailWord_5191178).sum := by decide
  have hdescent : baseEnd_5191178 < baseStart_5191178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191208 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5191208 : Nat := 118140960795 + 5191208 * 2 ^ 59
def prefixEnd_5191208 : Nat := 4983230072969 + 3 ^ 40 * 5191208 * 2
def baseEnd_5191208 : Nat := 888528293821810202842025

theorem tailTrace_5191208 : CollatzResearch.WordTrace tailWord_5191208 prefixEnd_5191208 888528293821810202842025 := by
  unfold tailWord_5191208
  simp only [CollatzResearch.WordTrace]
  refine ⟨94669455288573739293327139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126225940384764985724436185 94669455288573739293327139)
  ·
    refine ⟨142004182932860608939990709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94669455288573739293327139 142004182932860608939990709)
    ·
      refine ⟨13312892149955682088124129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142004182932860608939990709 13312892149955682088124129)
      ·
        refine ⟨9984669112466761566093097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13312892149955682088124129 9984669112466761566093097)
        ·
          refine ⟨7488501834350071174569823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9984669112466761566093097 7488501834350071174569823)
          ·
            refine ⟨11232752751525106761854735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7488501834350071174569823 11232752751525106761854735)
            ·
              refine ⟨16849129127287660142782103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11232752751525106761854735 16849129127287660142782103)
              ·
                refine ⟨25273693690931490214173155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16849129127287660142782103 25273693690931490214173155)
                ·
                  refine ⟨37910540536397235321259733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25273693690931490214173155 37910540536397235321259733)
                  ·
                    refine ⟨888528293821810202842025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37910540536397235321259733 888528293821810202842025)
                    ·
                      rfl

theorem cell23_5191208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5191208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191208 prefixEnd_5191208 := by exact prefixLift 5191208
  have htrace : WordTrace (prefixWord ++ tailWord_5191208) baseStart_5191208 baseEnd_5191208 := by
    simpa [prefixWord, tailWord_5191208, baseEnd_5191208] using wordTrace_append hprefix tailTrace_5191208
  have hstable : (prefixWord ++ tailWord_5191208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191208).length < 2 ^ (prefixWord ++ tailWord_5191208).sum := by decide
  have hdescent : baseEnd_5191208 < baseStart_5191208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191272 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 1, 4]
def baseStart_5191272 : Nat := 118140960795 + 5191272 * 2 ^ 59
def prefixEnd_5191272 : Nat := 4983230072969 + 3 ^ 40 * 5191272 * 2
def baseEnd_5191272 : Nat := 888539248075772786041927

theorem tailTrace_5191272 : CollatzResearch.WordTrace tailWord_5191272 prefixEnd_5191272 888539248075772786041927 := by
  unfold tailWord_5191272
  simp only [CollatzResearch.WordTrace]
  refine ⟨94670622424457808758492035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126227496565943745011322713 94670622424457808758492035)
  ·
    refine ⟨142005933636686713137738053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94670622424457808758492035 142005933636686713137738053)
    ·
      refine ⟨26626112556878758713325885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142005933636686713137738053 26626112556878758713325885)
      ·
        refine ⟨9984792208829534517497207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26626112556878758713325885 9984792208829534517497207)
        ·
          refine ⟨14977188313244301776245811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9984792208829534517497207 14977188313244301776245811)
          ·
            refine ⟨22465782469866452664368717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14977188313244301776245811 22465782469866452664368717)
            ·
              refine ⟨8424668426199919749138269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22465782469866452664368717 8424668426199919749138269)
              ·
                refine ⟨3159250659824969905926851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8424668426199919749138269 3159250659824969905926851)
                ·
                  refine ⟨4738875989737454858890277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159250659824969905926851 4738875989737454858890277)
                  ·
                    refine ⟨888539248075772786041927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4738875989737454858890277 888539248075772786041927)
                    ·
                      rfl

theorem cell23_5191272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_5191272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191272 prefixEnd_5191272 := by exact prefixLift 5191272
  have htrace : WordTrace (prefixWord ++ tailWord_5191272) baseStart_5191272 baseEnd_5191272 := by
    simpa [prefixWord, tailWord_5191272, baseEnd_5191272] using wordTrace_append hprefix tailTrace_5191272
  have hstable : (prefixWord ++ tailWord_5191272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191272).length < 2 ^ (prefixWord ++ tailWord_5191272).sum := by decide
  have hdescent : baseEnd_5191272 < baseStart_5191272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191328 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_5191328 : Nat := 118140960795 + 5191328 * 2 ^ 59
def prefixEnd_5191328 : Nat := 4983230072969 + 3 ^ 40 * 5191328 * 2
def baseEnd_5191328 : Nat := 888548833047990046341841

theorem tailTrace_5191328 : CollatzResearch.WordTrace tailWord_5191328 prefixEnd_5191328 888548833047990046341841 := by
  unfold tailWord_5191328
  simp only [CollatzResearch.WordTrace]
  refine ⟨94671643668356369540511319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126228858224475159387348425 94671643668356369540511319)
  ·
    refine ⟨142007465502534554310766979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94671643668356369540511319 142007465502534554310766979)
    ·
      refine ⟨213011198253801831466150469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142007465502534554310766979 213011198253801831466150469)
      ·
        refine ⟨39939599672587843399903213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213011198253801831466150469 39939599672587843399903213)
        ·
          refine ⟨14977349877220441274963705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39939599672587843399903213 14977349877220441274963705)
          ·
            refine ⟨11233012407915330956222779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14977349877220441274963705 11233012407915330956222779)
            ·
              refine ⟨16849518611872996434334169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11233012407915330956222779 16849518611872996434334169)
              ·
                refine ⟨12637138958904747325750627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16849518611872996434334169 12637138958904747325750627)
                ·
                  refine ⟨18955708438357120988625941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12637138958904747325750627 18955708438357120988625941)
                  ·
                    refine ⟨888548833047990046341841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18955708438357120988625941 888548833047990046341841)
                    ·
                      rfl

theorem cell23_5191328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_5191328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191328 prefixEnd_5191328 := by exact prefixLift 5191328
  have htrace : WordTrace (prefixWord ++ tailWord_5191328) baseStart_5191328 baseEnd_5191328 := by
    simpa [prefixWord, tailWord_5191328, baseEnd_5191328] using wordTrace_append hprefix tailTrace_5191328
  have hstable : (prefixWord ++ tailWord_5191328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191328).length < 2 ^ (prefixWord ++ tailWord_5191328).sum := by decide
  have hdescent : baseEnd_5191328 < baseStart_5191328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191358 : List Nat := [4, 2, 1, 1, 2, 2, 3, 8]
def baseStart_5191358 : Nat := 118140960795 + 5191358 * 2 ^ 59
def prefixEnd_5191358 : Nat := 4983230072969 + 3 ^ 40 * 5191358 * 2
def baseEnd_5191358 : Nat := 98728218650503889690755

theorem tailTrace_5191358 : CollatzResearch.WordTrace tailWord_5191358 prefixEnd_5191358 98728218650503889690755 := by
  unfold tailWord_5191358
  simp only [CollatzResearch.WordTrace]
  refine ⟨23668047690825506775576841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126229587684402702803076485 23668047690825506775576841)
  ·
    refine ⟨17751035768119130081682631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23668047690825506775576841 17751035768119130081682631)
    ·
      refine ⟨26626553652178695122523947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17751035768119130081682631 26626553652178695122523947)
      ·
        refine ⟨39939830478268042683785921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26626553652178695122523947 39939830478268042683785921)
        ·
          refine ⟨29954872858701032012839441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39939830478268042683785921 29954872858701032012839441)
          ·
            refine ⟨22466154644025774009629581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29954872858701032012839441 22466154644025774009629581)
            ·
              refine ⟨8424807991509665253611093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22466154644025774009629581 8424807991509665253611093)
              ·
                refine ⟨98728218650503889690755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8424807991509665253611093 98728218650503889690755)
                ·
                  rfl

theorem cell23_5191358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_5191358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191358 prefixEnd_5191358 := by exact prefixLift 5191358
  have htrace : WordTrace (prefixWord ++ tailWord_5191358) baseStart_5191358 baseEnd_5191358 := by
    simpa [prefixWord, tailWord_5191358, baseEnd_5191358] using wordTrace_append hprefix tailTrace_5191358
  have hstable : (prefixWord ++ tailWord_5191358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191358).length < 2 ^ (prefixWord ++ tailWord_5191358).sum := by decide
  have hdescent : baseEnd_5191358 < baseStart_5191358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191389 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5191389 : Nat := 118140960795 + 5191389 * 2 ^ 59
def prefixEnd_5191389 : Nat := 4983230072969 + 3 ^ 40 * 5191389 * 2
def baseEnd_5191389 : Nat := 2665677821463894400362743

theorem tailTrace_5191389 : CollatzResearch.WordTrace tailWord_5191389 prefixEnd_5191389 2665677821463894400362743 := by
  unfold tailWord_5191389
  simp only [CollatzResearch.WordTrace]
  refine ⟨189345512189491746498993221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126230341459661164332662147 189345512189491746498993221)
  ·
    refine ⟨35502283535529702468561229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189345512189491746498993221 35502283535529702468561229)
    ·
      refine ⟨13313356325823638425710461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35502283535529702468561229 13313356325823638425710461)
      ·
        refine ⟨4992508622183864409641423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13313356325823638425710461 4992508622183864409641423)
        ·
          refine ⟨7488762933275796614462135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992508622183864409641423 7488762933275796614462135)
          ·
            refine ⟨11233144399913694921693203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7488762933275796614462135 11233144399913694921693203)
            ·
              refine ⟨16849716599870542382539805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11233144399913694921693203 16849716599870542382539805)
              ·
                refine ⟨6318643724951453393452427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16849716599870542382539805 6318643724951453393452427)
                ·
                  refine ⟨9477965587427180090178641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6318643724951453393452427 9477965587427180090178641)
                  ·
                    refine ⟨7108474190570385067633981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9477965587427180090178641 7108474190570385067633981)
                    ·
                      refine ⟨2665677821463894400362743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7108474190570385067633981 2665677821463894400362743)
                      ·
                        rfl

theorem cell23_5191389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5191389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191389 prefixEnd_5191389 := by exact prefixLift 5191389
  have htrace : WordTrace (prefixWord ++ tailWord_5191389) baseStart_5191389 baseEnd_5191389 := by
    simpa [prefixWord, tailWord_5191389, baseEnd_5191389] using wordTrace_append hprefix tailTrace_5191389
  have hstable : (prefixWord ++ tailWord_5191389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191389).length < 2 ^ (prefixWord ++ tailWord_5191389).sum := by decide
  have hdescent : baseEnd_5191389 < baseStart_5191389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191402 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_5191402 : Nat := 118140960795 + 5191402 * 2 ^ 59
def prefixEnd_5191402 : Nat := 4983230072969 + 3 ^ 40 * 5191402 * 2
def baseEnd_5191402 : Nat := 2665684496712402849500183

theorem tailTrace_5191402 : CollatzResearch.WordTrace tailWord_5191402 prefixEnd_5191402 2665684496712402849500183 := by
  unfold tailWord_5191402
  simp only [CollatzResearch.WordTrace]
  refine ⟨47336496584611162429804115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126230657558963099812810973 47336496584611162429804115)
  ·
    refine ⟨71004744876916743644706173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47336496584611162429804115 71004744876916743644706173)
    ·
      refine ⟨26626779328843778866764815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71004744876916743644706173 26626779328843778866764815)
      ·
        refine ⟨39940168993265668300147223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26626779328843778866764815 39940168993265668300147223)
        ·
          refine ⟨59910253489898502450220835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39940168993265668300147223 59910253489898502450220835)
          ·
            refine ⟨89865380234847753675331253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59910253489898502450220835 89865380234847753675331253)
            ·
              refine ⟨8424879397016976907062305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89865380234847753675331253 8424879397016976907062305)
              ·
                refine ⟨6318659547762732680296729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8424879397016976907062305 6318659547762732680296729)
                ·
                  refine ⟨4738994660822049510222547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6318659547762732680296729 4738994660822049510222547)
                  ·
                    refine ⟨7108491991233074265333821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4738994660822049510222547 7108491991233074265333821)
                    ·
                      refine ⟨2665684496712402849500183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7108491991233074265333821 2665684496712402849500183)
                      ·
                        rfl

theorem cell23_5191402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_5191402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191402 prefixEnd_5191402 := by exact prefixLift 5191402
  have htrace : WordTrace (prefixWord ++ tailWord_5191402) baseStart_5191402 baseEnd_5191402 := by
    simpa [prefixWord, tailWord_5191402, baseEnd_5191402] using wordTrace_append hprefix tailTrace_5191402
  have hstable : (prefixWord ++ tailWord_5191402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191402).length < 2 ^ (prefixWord ++ tailWord_5191402).sum := by decide
  have hdescent : baseEnd_5191402 < baseStart_5191402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191438 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_5191438 : Nat := 118140960795 + 5191438 * 2 ^ 59
def prefixEnd_5191438 : Nat := 4983230072969 + 3 ^ 40 * 5191438 * 2
def baseEnd_5191438 : Nat := 2665702982015964708650017

theorem tailTrace_5191438 : CollatzResearch.WordTrace tailWord_5191438 prefixEnd_5191438 2665702982015964708650017 := by
  unfold tailWord_5191438
  simp only [CollatzResearch.WordTrace]
  refine ⟨23668412420789278483440871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126231532910876151911684645 23668412420789278483440871)
  ·
    refine ⟨35502618631183917725161307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23668412420789278483440871 35502618631183917725161307)
    ·
      refine ⟨53253927946775876587741961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35502618631183917725161307 53253927946775876587741961)
      ·
        refine ⟨39940445960081907440806471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53253927946775876587741961 39940445960081907440806471)
        ·
          refine ⟨59910668940122861161209707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39940445960081907440806471 59910668940122861161209707)
          ·
            refine ⟨89866003410184291741814561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59910668940122861161209707 89866003410184291741814561)
            ·
              refine ⟨67399502557638218806360921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89866003410184291741814561 67399502557638218806360921)
              ·
                refine ⟨50549626918228664104770691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67399502557638218806360921 50549626918228664104770691)
                ·
                  refine ⟨75824440377342996157156037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50549626918228664104770691 75824440377342996157156037)
                  ·
                    refine ⟨14217082570751811779466757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75824440377342996157156037 14217082570751811779466757)
                    ·
                      refine ⟨2665702982015964708650017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14217082570751811779466757 2665702982015964708650017)
                      ·
                        rfl

theorem cell23_5191438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_5191438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191438 prefixEnd_5191438 := by exact prefixLift 5191438
  have htrace : WordTrace (prefixWord ++ tailWord_5191438) baseStart_5191438 baseEnd_5191438 := by
    simpa [prefixWord, tailWord_5191438, baseEnd_5191438] using wordTrace_append hprefix tailTrace_5191438
  have hstable : (prefixWord ++ tailWord_5191438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191438).length < 2 ^ (prefixWord ++ tailWord_5191438).sum := by decide
  have hdescent : baseEnd_5191438 < baseStart_5191438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191458 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5191458 : Nat := 118140960795 + 5191458 * 2 ^ 59
def prefixEnd_5191458 : Nat := 4983230072969 + 3 ^ 40 * 5191458 * 2
def baseEnd_5191458 : Nat := 2665713251629054630399925

theorem tailTrace_5191458 : CollatzResearch.WordTrace tailWord_5191458 prefixEnd_5191458 2665713251629054630399925 := by
  unfold tailWord_5191458
  simp only [CollatzResearch.WordTrace]
  refine ⟨47337007206560442820813757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126232019217494514188836685 47337007206560442820813757)
  ·
    refine ⟨17751377702460166057805159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47337007206560442820813757 17751377702460166057805159)
    ·
      refine ⟨26627066553690249086707739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17751377702460166057805159 26627066553690249086707739)
      ·
        refine ⟨39940599830535373630061609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26627066553690249086707739 39940599830535373630061609)
        ·
          refine ⟨29955449872901530222546207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39940599830535373630061609 29955449872901530222546207)
          ·
            refine ⟨44933174809352295333819311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29955449872901530222546207 44933174809352295333819311)
            ·
              refine ⟨67399762214028443000728967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44933174809352295333819311 67399762214028443000728967)
              ·
                refine ⟨101099643321042664501093451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67399762214028443000728967 101099643321042664501093451)
                ·
                  refine ⟨151649464981563996751640177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101099643321042664501093451 151649464981563996751640177)
                  ·
                    refine ⟨113737098736172997563730133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151649464981563996751640177 113737098736172997563730133)
                    ·
                      refine ⟨2665713251629054630399925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113737098736172997563730133 2665713251629054630399925)
                      ·
                        rfl

theorem cell23_5191458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5191458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191458 prefixEnd_5191458 := by exact prefixLift 5191458
  have htrace : WordTrace (prefixWord ++ tailWord_5191458) baseStart_5191458 baseEnd_5191458 := by
    simpa [prefixWord, tailWord_5191458, baseEnd_5191458] using wordTrace_append hprefix tailTrace_5191458
  have hstable : (prefixWord ++ tailWord_5191458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191458).length < 2 ^ (prefixWord ++ tailWord_5191458).sum := by decide
  have hdescent : baseEnd_5191458 < baseStart_5191458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191476 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5191476 : Nat := 118140960795 + 5191476 * 2 ^ 59
def prefixEnd_5191476 : Nat := 4983230072969 + 3 ^ 40 * 5191476 * 2
def baseEnd_5191476 : Nat := 2665722494280835559974843

theorem tailTrace_5191476 : CollatzResearch.WordTrace tailWord_5191476 prefixEnd_5191476 2665722494280835559974843 := by
  unfold tailWord_5191476
  simp only [CollatzResearch.WordTrace]
  refine ⟨94674342670088280178705141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126232456893451040238273521 94674342670088280178705141)
  ·
    refine ⟨8875719625320776266753607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94674342670088280178705141 8875719625320776266753607)
    ·
      refine ⟨13313579437981164400130411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8875719625320776266753607 13313579437981164400130411)
      ·
        refine ⟨19970369156971746600195617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13313579437981164400130411 19970369156971746600195617)
        ·
          refine ⟨14977776867728809950146713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19970369156971746600195617 14977776867728809950146713)
          ·
            refine ⟨11233332650796607462610035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14977776867728809950146713 11233332650796607462610035)
            ·
              refine ⟨16849998976194911193915053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11233332650796607462610035 16849998976194911193915053)
              ·
                refine ⟨6318749616073091697718145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16849998976194911193915053 6318749616073091697718145)
                ·
                  refine ⟨4739062212054818773288609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6318749616073091697718145 4739062212054818773288609)
                  ·
                    refine ⟨3554296659041114079966457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4739062212054818773288609 3554296659041114079966457)
                    ·
                      refine ⟨2665722494280835559974843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554296659041114079966457 2665722494280835559974843)
                      ·
                        rfl

theorem cell23_5191476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5191476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191476 prefixEnd_5191476 := by exact prefixLift 5191476
  have htrace : WordTrace (prefixWord ++ tailWord_5191476) baseStart_5191476 baseEnd_5191476 := by
    simpa [prefixWord, tailWord_5191476, baseEnd_5191476] using wordTrace_append hprefix tailTrace_5191476
  have hstable : (prefixWord ++ tailWord_5191476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191476).length < 2 ^ (prefixWord ++ tailWord_5191476).sum := by decide
  have hdescent : baseEnd_5191476 < baseStart_5191476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191516 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 5]
def baseStart_5191516 : Nat := 118140960795 + 5191516 * 2 ^ 59
def prefixEnd_5191516 : Nat := 4983230072969 + 3 ^ 40 * 5191516 * 2
def baseEnd_5191516 : Nat := 296193670389668378163851

theorem tailTrace_5191516 : CollatzResearch.WordTrace tailWord_5191516 prefixEnd_5191516 296193670389668378163851 := by
  unfold tailWord_5191516
  simp only [CollatzResearch.WordTrace]
  refine ⟨94675072130015823594433201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126233429506687764792577601 94675072130015823594433201)
  ·
    refine ⟨71006304097511867695824901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94675072130015823594433201 71006304097511867695824901)
    ·
      refine ⟨13313682018283475192967169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71006304097511867695824901 13313682018283475192967169)
      ·
        refine ⟨9985261513712606394725377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13313682018283475192967169 9985261513712606394725377)
        ·
          refine ⟨7488946135284454796044033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9985261513712606394725377 7488946135284454796044033)
          ·
            refine ⟨5616709601463341097033025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7488946135284454796044033 5616709601463341097033025)
            ·
              refine ⟨4212532201097505822774769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616709601463341097033025 4212532201097505822774769)
              ·
                refine ⟨3159399150823129367081077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212532201097505822774769 3159399150823129367081077)
                ·
                  refine ⟨296193670389668378163851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3159399150823129367081077 296193670389668378163851)
                  ·
                    rfl

theorem cell23_5191516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_5191516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191516 prefixEnd_5191516 := by exact prefixLift 5191516
  have htrace : WordTrace (prefixWord ++ tailWord_5191516) baseStart_5191516 baseEnd_5191516 := by
    simpa [prefixWord, tailWord_5191516, baseEnd_5191516] using wordTrace_append hprefix tailTrace_5191516
  have hstable : (prefixWord ++ tailWord_5191516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191516).length < 2 ^ (prefixWord ++ tailWord_5191516).sum := by decide
  have hdescent : baseEnd_5191516 < baseStart_5191516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191525 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_5191525 : Nat := 118140960795 + 5191525 * 2 ^ 59
def prefixEnd_5191525 : Nat := 4983230072969 + 3 ^ 40 * 5191525 * 2
def baseEnd_5191525 : Nat := 888582551610968622754039

theorem tailTrace_5191525 : CollatzResearch.WordTrace tailWord_5191525 prefixEnd_5191525 888582551610968622754039 := by
  unfold tailWord_5191525
  simp only [CollatzResearch.WordTrace]
  refine ⟨189350472516999041725944029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126233648344666027817296019 189350472516999041725944029)
  ·
    refine ⟨71006427193874640647229011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189350472516999041725944029 71006427193874640647229011)
    ·
      refine ⟨106509640790811960970843517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71006427193874640647229011 106509640790811960970843517)
      ·
        refine ⟨39941115296554485364066319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106509640790811960970843517 39941115296554485364066319)
        ·
          refine ⟨59911672944831728046099479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39941115296554485364066319 59911672944831728046099479)
          ·
            refine ⟨89867509417247592069149219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59911672944831728046099479 89867509417247592069149219)
            ·
              refine ⟨134801264125871388103723829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89867509417247592069149219 134801264125871388103723829)
              ·
                refine ⟨12637618511800442634724109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134801264125871388103723829 12637618511800442634724109)
                ·
                  refine ⟨4739106941925165988021541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12637618511800442634724109 4739106941925165988021541)
                  ·
                    refine ⟨888582551610968622754039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739106941925165988021541 888582551610968622754039)
                    ·
                      rfl

theorem cell23_5191525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_5191525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191525 prefixEnd_5191525 := by exact prefixLift 5191525
  have htrace : WordTrace (prefixWord ++ tailWord_5191525) baseStart_5191525 baseEnd_5191525 := by
    simpa [prefixWord, tailWord_5191525, baseEnd_5191525] using wordTrace_append hprefix tailTrace_5191525
  have hstable : (prefixWord ++ tailWord_5191525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191525).length < 2 ^ (prefixWord ++ tailWord_5191525).sum := by decide
  have hdescent : baseEnd_5191525 < baseStart_5191525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191532 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 2, 4, 2]
def baseStart_5191532 : Nat := 118140960795 + 5191532 * 2 ^ 59
def prefixEnd_5191532 : Nat := 4983230072969 + 3 ^ 40 * 5191532 * 2
def baseEnd_5191532 : Nat := 2665751249197487340874585

theorem tailTrace_5191532 : CollatzResearch.WordTrace tailWord_5191532 prefixEnd_5191532 2665751249197487340874585 := by
  unfold tailWord_5191532
  simp only [CollatzResearch.WordTrace]
  refine ⟨94675363913986840960724425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126233818551982454614299233 94675363913986840960724425)
  ·
    refine ⟨71006522935490130720543319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94675363913986840960724425 71006522935490130720543319)
    ·
      refine ⟨106509784403235196080814979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71006522935490130720543319 106509784403235196080814979)
      ·
        refine ⟨159764676604852794121222469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106509784403235196080814979 159764676604852794121222469)
        ·
          refine ⟨29955876863409898897729213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159764676604852794121222469 29955876863409898897729213)
          ·
            refine ⟨11233453823778712086648455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29955876863409898897729213 11233453823778712086648455)
            ·
              refine ⟨16850180735668068129972683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11233453823778712086648455 16850180735668068129972683)
              ·
                refine ⟨25275271103502102194959025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16850180735668068129972683 25275271103502102194959025)
                ·
                  refine ⟨18956453327626576646219269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25275271103502102194959025 18956453327626576646219269)
                  ·
                    refine ⟨3554334998929983121166113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18956453327626576646219269 3554334998929983121166113)
                    ·
                      refine ⟨2665751249197487340874585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554334998929983121166113 2665751249197487340874585)
                      ·
                        rfl

theorem cell23_5191532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_5191532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191532 prefixEnd_5191532 := by exact prefixLift 5191532
  have htrace : WordTrace (prefixWord ++ tailWord_5191532) baseStart_5191532 baseEnd_5191532 := by
    simpa [prefixWord, tailWord_5191532, baseEnd_5191532] using wordTrace_append hprefix tailTrace_5191532
  have hstable : (prefixWord ++ tailWord_5191532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191532).length < 2 ^ (prefixWord ++ tailWord_5191532).sum := by decide
  have hdescent : baseEnd_5191532 < baseStart_5191532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191538 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_5191538 : Nat := 118140960795 + 5191538 * 2 ^ 59
def prefixEnd_5191538 : Nat := 4983230072969 + 3 ^ 40 * 5191538 * 2
def baseEnd_5191538 : Nat := 296194925564601590822173

theorem tailTrace_5191538 : CollatzResearch.WordTrace tailWord_5191538 prefixEnd_5191538 296194925564601590822173 := by
  unfold tailWord_5191538
  simp only [CollatzResearch.WordTrace]
  refine ⟨47337736666487986236541817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126233964443967963297444845 47337736666487986236541817)
  ·
    refine ⟨35503302499865989677406363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47337736666487986236541817 35503302499865989677406363)
    ·
      refine ⟨53254953749798984516109545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35503302499865989677406363 53254953749798984516109545)
      ·
        refine ⟨39941215312349238387082159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53254953749798984516109545 39941215312349238387082159)
        ·
          refine ⟨59911822968523857580623239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39941215312349238387082159 59911822968523857580623239)
          ·
            refine ⟨89867734452785786370934859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59911822968523857580623239 89867734452785786370934859)
            ·
              refine ⟨134801601679178679556402289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89867734452785786370934859 134801601679178679556402289)
              ·
                refine ⟨101101201259384009667301717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134801601679178679556402289 101101201259384009667301717)
                ·
                  refine ⟨296194925564601590822173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 101101201259384009667301717 296194925564601590822173)
                  ·
                    rfl

theorem cell23_5191538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_5191538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191538 prefixEnd_5191538 := by exact prefixLift 5191538
  have htrace : WordTrace (prefixWord ++ tailWord_5191538) baseStart_5191538 baseEnd_5191538 := by
    simpa [prefixWord, tailWord_5191538, baseEnd_5191538] using wordTrace_append hprefix tailTrace_5191538
  have hstable : (prefixWord ++ tailWord_5191538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191538).length < 2 ^ (prefixWord ++ tailWord_5191538).sum := by decide
  have hdescent : baseEnd_5191538 < baseStart_5191538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191572 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 6]
def baseStart_5191572 : Nat := 118140960795 + 5191572 * 2 ^ 59
def prefixEnd_5191572 : Nat := 4983230072969 + 3 ^ 40 * 5191572 * 2
def baseEnd_5191572 : Nat := 296196865380407464930489

theorem tailTrace_5191572 : CollatzResearch.WordTrace tailWord_5191572 prefixEnd_5191572 296196865380407464930489 := by
  unfold tailWord_5191572
  simp only [CollatzResearch.WordTrace]
  refine ⟨94676093373914384376452485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126234791165219179168603313 94676093373914384376452485)
  ·
    refine ⟨17751767507608947070584841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94676093373914384376452485 17751767507608947070584841)
    ·
      refine ⟨13313825630706710302938631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17751767507608947070584841 13313825630706710302938631)
      ·
        refine ⟨19970738446060065454407947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13313825630706710302938631 19970738446060065454407947)
        ·
          refine ⟨29956107669090098181611921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19970738446060065454407947 29956107669090098181611921)
          ·
            refine ⟨22467080751817573636208941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29956107669090098181611921 22467080751817573636208941)
            ·
              refine ⟨8425155281931590113578353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22467080751817573636208941 8425155281931590113578353)
              ·
                refine ⟨6318866461448692585183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8425155281931590113578353 6318866461448692585183765)
                ·
                  refine ⟨296196865380407464930489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6318866461448692585183765 296196865380407464930489)
                  ·
                    rfl

theorem cell23_5191572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_5191572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191572 prefixEnd_5191572 := by exact prefixLift 5191572
  have htrace : WordTrace (prefixWord ++ tailWord_5191572) baseStart_5191572 baseEnd_5191572 := by
    simpa [prefixWord, tailWord_5191572, baseEnd_5191572] using wordTrace_append hprefix tailTrace_5191572
  have hstable : (prefixWord ++ tailWord_5191572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191572).length < 2 ^ (prefixWord ++ tailWord_5191572).sum := by decide
  have hdescent : baseEnd_5191572 < baseStart_5191572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191615 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 6, 4]
def baseStart_5191615 : Nat := 118140960795 + 5191615 * 2 ^ 59
def prefixEnd_5191615 : Nat := 4983230072969 + 3 ^ 40 * 5191615 * 2
def baseEnd_5191615 : Nat := 888597956030603505378901

theorem tailTrace_5191615 : CollatzResearch.WordTrace tailWord_5191615 prefixEnd_5191615 888597956030603505378901 := by
  unfold tailWord_5191615
  simp only [CollatzResearch.WordTrace]
  refine ⟨189353755086672987096720299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126235836724448658064480199 189353755086672987096720299)
  ·
    refine ⟨284030632630009480645080449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189353755086672987096720299 284030632630009480645080449)
    ·
      refine ⟨213022974472507110483810337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284030632630009480645080449 213022974472507110483810337)
      ·
        refine ⟨159767230854380332862857753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213022974472507110483810337 159767230854380332862857753)
        ·
          refine ⟨119825423140785249647143315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159767230854380332862857753 119825423140785249647143315)
          ·
            refine ⟨179738134711177874470714973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119825423140785249647143315 179738134711177874470714973)
            ·
              refine ⟨67401800516691702926518115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179738134711177874470714973 67401800516691702926518115)
              ·
                refine ⟨101102700775037554389777173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67401800516691702926518115 101102700775037554389777173)
                ·
                  refine ⟨4739189098829885362020805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101102700775037554389777173 4739189098829885362020805)
                  ·
                    refine ⟨888597956030603505378901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739189098829885362020805 888597956030603505378901)
                    ·
                      rfl

theorem cell23_5191615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_5191615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191615 prefixEnd_5191615 := by exact prefixLift 5191615
  have htrace : WordTrace (prefixWord ++ tailWord_5191615) baseStart_5191615 baseEnd_5191615 := by
    simpa [prefixWord, tailWord_5191615, baseEnd_5191615] using wordTrace_append hprefix tailTrace_5191615
  have hstable : (prefixWord ++ tailWord_5191615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191615).length < 2 ^ (prefixWord ++ tailWord_5191615).sum := by decide
  have hdescent : baseEnd_5191615 < baseStart_5191615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191649 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 2, 4]
def baseStart_5191649 : Nat := 118140960795 + 5191649 * 2 ^ 59
def prefixEnd_5191649 : Nat := 4983230072969 + 3 ^ 40 * 5191649 * 2
def baseEnd_5191649 : Nat := 888603775478021127703849

theorem tailTrace_5191649 : CollatzResearch.WordTrace tailWord_5191649 prefixEnd_5191649 888603775478021127703849 := by
  unfold tailWord_5191649
  simp only [CollatzResearch.WordTrace]
  refine ⟨189354995168549810903458001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126236663445699873935638667 189354995168549810903458001)
  ·
    refine ⟨142016246376412358177593501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189354995168549810903458001 142016246376412358177593501)
    ·
      refine ⟨53256092391154634316597563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142016246376412358177593501 53256092391154634316597563)
      ·
        refine ⟨79884138586731951474896345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53256092391154634316597563 79884138586731951474896345)
        ·
          refine ⟨59913103940048963606172259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79884138586731951474896345 59913103940048963606172259)
          ·
            refine ⟨89869655910073445409258389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59913103940048963606172259 89869655910073445409258389)
            ·
              refine ⟨4212640120784692753558987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89869655910073445409258389 4212640120784692753558987)
              ·
                refine ⟨6318960181177039130338481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4212640120784692753558987 6318960181177039130338481)
                ·
                  refine ⟨4739220135882779347753861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6318960181177039130338481 4739220135882779347753861)
                  ·
                    refine ⟨888603775478021127703849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739220135882779347753861 888603775478021127703849)
                    ·
                      rfl

theorem cell23_5191649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_5191649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191649 prefixEnd_5191649 := by exact prefixLift 5191649
  have htrace : WordTrace (prefixWord ++ tailWord_5191649) baseStart_5191649 baseEnd_5191649 := by
    simpa [prefixWord, tailWord_5191649, baseEnd_5191649] using wordTrace_append hprefix tailTrace_5191649
  have hstable : (prefixWord ++ tailWord_5191649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191649).length < 2 ^ (prefixWord ++ tailWord_5191649).sum := by decide
  have hdescent : baseEnd_5191649 < baseStart_5191649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191672 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_5191672 : Nat := 118140960795 + 5191672 * 2 ^ 59
def prefixEnd_5191672 : Nat := 4983230072969 + 3 ^ 40 * 5191672 * 2
def baseEnd_5191672 : Nat := 2665823136489116793123941

theorem tailTrace_5191672 : CollatzResearch.WordTrace tailWord_5191672 prefixEnd_5191672 2665823136489116793123941 := by
  unfold tailWord_5191672
  simp only [CollatzResearch.WordTrace]
  refine ⟨94677917023733242915772635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126237222698310990554363513 94677917023733242915772635)
  ·
    refine ⟨142016875535599864373658953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94677917023733242915772635 142016875535599864373658953)
    ·
      refine ⟨106512656651699898280244215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142016875535599864373658953 106512656651699898280244215)
      ·
        refine ⟨159768984977549847420366323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106512656651699898280244215 159768984977549847420366323)
        ·
          refine ⟨239653477466324771130549485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159768984977549847420366323 239653477466324771130549485)
          ·
            refine ⟨89870054049871789173956057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239653477466324771130549485 89870054049871789173956057)
            ·
              refine ⟨67402540537403841880467043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89870054049871789173956057 67402540537403841880467043)
              ·
                refine ⟨101103810806105762820700565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67402540537403841880467043 101103810806105762820700565)
                ·
                  refine ⟨4739241131536207632220339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101103810806105762820700565 4739241131536207632220339)
                  ·
                    refine ⟨7108861697304311448330509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4739241131536207632220339 7108861697304311448330509)
                    ·
                      refine ⟨2665823136489116793123941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7108861697304311448330509 2665823136489116793123941)
                      ·
                        rfl

theorem cell23_5191672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_5191672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191672 prefixEnd_5191672 := by exact prefixLift 5191672
  have htrace : WordTrace (prefixWord ++ tailWord_5191672) baseStart_5191672 baseEnd_5191672 := by
    simpa [prefixWord, tailWord_5191672, baseEnd_5191672] using wordTrace_append hprefix tailTrace_5191672
  have hstable : (prefixWord ++ tailWord_5191672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191672).length < 2 ^ (prefixWord ++ tailWord_5191672).sum := by decide
  have hdescent : baseEnd_5191672 < baseStart_5191672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191729 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 1, 4, 2]
def baseStart_5191729 : Nat := 118140960795 + 5191729 * 2 ^ 59
def prefixEnd_5191729 : Nat := 4983230072969 + 3 ^ 40 * 5191729 * 2
def baseEnd_5191729 : Nat := 2665852404886423070111179

theorem tailTrace_5191729 : CollatzResearch.WordTrace tailWord_5191729 prefixEnd_5191729 2665852404886423070111179 := by
  unfold tailWord_5191729
  simp only [CollatzResearch.WordTrace]
  refine ⟨189357913008259984566370241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126238608672173323044246827 189357913008259984566370241)
  ·
    refine ⟨142018434756194988424777681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189357913008259984566370241 142018434756194988424777681)
    ·
      refine ⟨106513826067146241318583261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142018434756194988424777681 106513826067146241318583261)
      ·
        refine ⟨39942684775179840494468723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106513826067146241318583261 39942684775179840494468723)
        ·
          refine ⟨59914027162769760741703085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39942684775179840494468723 59914027162769760741703085)
          ·
            refine ⟨22467760186038660278138657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59914027162769760741703085 22467760186038660278138657)
            ·
              refine ⟨16850820139528995208603993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22467760186038660278138657 16850820139528995208603993)
              ·
                refine ⟨12638115104646746406452995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16850820139528995208603993 12638115104646746406452995)
                ·
                  refine ⟨18957172656970119609679493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12638115104646746406452995 18957172656970119609679493)
                  ·
                    refine ⟨3554469873181897426814905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18957172656970119609679493 3554469873181897426814905)
                    ·
                      refine ⟨2665852404886423070111179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554469873181897426814905 2665852404886423070111179)
                      ·
                        rfl

theorem cell23_5191729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_5191729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191729 prefixEnd_5191729 := by exact prefixLift 5191729
  have htrace : WordTrace (prefixWord ++ tailWord_5191729) baseStart_5191729 baseEnd_5191729 := by
    simpa [prefixWord, tailWord_5191729, baseEnd_5191729] using wordTrace_append hprefix tailTrace_5191729
  have hstable : (prefixWord ++ tailWord_5191729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191729).length < 2 ^ (prefixWord ++ tailWord_5191729).sum := by decide
  have hdescent : baseEnd_5191729 < baseStart_5191729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191775 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5191775 : Nat := 118140960795 + 5191775 * 2 ^ 59
def prefixEnd_5191775 : Nat := 4983230072969 + 3 ^ 40 * 5191775 * 2
def baseEnd_5191775 : Nat := 2665876024996529890135967

theorem tailTrace_5191775 : CollatzResearch.WordTrace tailWord_5191775 prefixEnd_5191775 2665876024996529890135967 := by
  unfold tailWord_5191775
  simp only [CollatzResearch.WordTrace]
  refine ⟨189359590766093334422544779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126239727177395556281696519 189359590766093334422544779)
  ·
    refine ⟨284039386149140001633817169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189359590766093334422544779 284039386149140001633817169)
    ·
      refine ⟨213029539611855001225362877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284039386149140001633817169 213029539611855001225362877)
      ·
        refine ⟨79886077354445625459511079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213029539611855001225362877 79886077354445625459511079)
        ·
          refine ⟨119829116031668438189266619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79886077354445625459511079 119829116031668438189266619)
          ·
            refine ⟨179743674047502657283899929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119829116031668438189266619 179743674047502657283899929)
            ·
              refine ⟨134807755535626992962924947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179743674047502657283899929 134807755535626992962924947)
              ·
                refine ⟨202211633303440489444387421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134807755535626992962924947 202211633303440489444387421)
                ·
                  refine ⟨75829362488790183541645283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202211633303440489444387421 75829362488790183541645283)
                  ·
                    refine ⟨113744043733185275312467925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75829362488790183541645283 113744043733185275312467925)
                    ·
                      refine ⟨2665876024996529890135967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113744043733185275312467925 2665876024996529890135967)
                      ·
                        rfl

theorem cell23_5191775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5191775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191775 prefixEnd_5191775 := by exact prefixLift 5191775
  have htrace : WordTrace (prefixWord ++ tailWord_5191775) baseStart_5191775 baseEnd_5191775 := by
    simpa [prefixWord, tailWord_5191775, baseEnd_5191775] using wordTrace_append hprefix tailTrace_5191775
  have hstable : (prefixWord ++ tailWord_5191775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191775).length < 2 ^ (prefixWord ++ tailWord_5191775).sum := by decide
  have hdescent : baseEnd_5191775 < baseStart_5191775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191809 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_5191809 : Nat := 118140960795 + 5191809 * 2 ^ 59
def prefixEnd_5191809 : Nat := 4983230072969 + 3 ^ 40 * 5191809 * 2
def baseEnd_5191809 : Nat := 2665893483338782757110811

theorem tailTrace_5191809 : CollatzResearch.WordTrace tailWord_5191809 prefixEnd_5191809 2665893483338782757110811 := by
  unfold tailWord_5191809
  simp only [CollatzResearch.WordTrace]
  refine ⟨189360830847970158229282481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126240553898646772152854987 189360830847970158229282481)
  ·
    refine ⟨142020623135977618671961861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189360830847970158229282481 142020623135977618671961861)
    ·
      refine ⟨26628866837995803500992849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142020623135977618671961861 26628866837995803500992849)
      ·
        refine ⟨19971650128496852625744637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26628866837995803500992849 19971650128496852625744637)
        ·
          refine ⟨7489368798186319734654239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19971650128496852625744637 7489368798186319734654239)
          ·
            refine ⟨11234053197279479601981359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7489368798186319734654239 11234053197279479601981359)
            ·
              refine ⟨16851079795919219402972039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11234053197279479601981359 16851079795919219402972039)
              ·
                refine ⟨25276619693878829104458059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16851079795919219402972039 25276619693878829104458059)
                ·
                  refine ⟨37914929540818243656687089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25276619693878829104458059 37914929540818243656687089)
                  ·
                    refine ⟨28436197155613682742515317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37914929540818243656687089 28436197155613682742515317)
                    ·
                      refine ⟨2665893483338782757110811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28436197155613682742515317 2665893483338782757110811)
                      ·
                        rfl

theorem cell23_5191809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_5191809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191809 prefixEnd_5191809 := by exact prefixLift 5191809
  have htrace : WordTrace (prefixWord ++ tailWord_5191809) baseStart_5191809 baseEnd_5191809 := by
    simpa [prefixWord, tailWord_5191809, baseEnd_5191809] using wordTrace_append hprefix tailTrace_5191809
  have hstable : (prefixWord ++ tailWord_5191809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191809).length < 2 ^ (prefixWord ++ tailWord_5191809).sum := by decide
  have hdescent : baseEnd_5191809 < baseStart_5191809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191852 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_5191852 : Nat := 118140960795 + 5191852 * 2 ^ 59
def prefixEnd_5191852 : Nat := 4983230072969 + 3 ^ 40 * 5191852 * 2
def baseEnd_5191852 : Nat := 2665915563006926088873113

theorem tailTrace_5191852 : CollatzResearch.WordTrace tailWord_5191852 prefixEnd_5191852 2665915563006926088873113 := by
  unfold tailWord_5191852
  simp only [CollatzResearch.WordTrace]
  refine ⟨94681199593407188286548905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126241599457876251048731873 94681199593407188286548905)
  ·
    refine ⟨71010899695055391214911679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94681199593407188286548905 71010899695055391214911679)
    ·
      refine ⟨106516349542583086822367519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71010899695055391214911679 106516349542583086822367519)
      ·
        refine ⟨159774524313874630233551279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106516349542583086822367519 159774524313874630233551279)
        ·
          refine ⟨239661786470811945350326919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159774524313874630233551279 239661786470811945350326919)
          ·
            refine ⟨359492679706217918025490379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239661786470811945350326919 359492679706217918025490379)
            ·
              refine ⟨539239019559326877038235569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359492679706217918025490379 539239019559326877038235569)
              ·
                refine ⟨404429264669495157778676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539239019559326877038235569 404429264669495157778676677)
                ·
                  refine ⟨75830487125530342083501877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404429264669495157778676677 75830487125530342083501877)
                  ·
                    refine ⟨7109108168018469570328301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75830487125530342083501877 7109108168018469570328301)
                    ·
                      refine ⟨2665915563006926088873113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7109108168018469570328301 2665915563006926088873113)
                      ·
                        rfl

theorem cell23_5191852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_5191852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191852 prefixEnd_5191852 := by exact prefixLift 5191852
  have htrace : WordTrace (prefixWord ++ tailWord_5191852) baseStart_5191852 baseEnd_5191852 := by
    simpa [prefixWord, tailWord_5191852, baseEnd_5191852] using wordTrace_append hprefix tailTrace_5191852
  have hstable : (prefixWord ++ tailWord_5191852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191852).length < 2 ^ (prefixWord ++ tailWord_5191852).sum := by decide
  have hdescent : baseEnd_5191852 < baseStart_5191852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191863 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 1, 4]
def baseStart_5191863 : Nat := 118140960795 + 5191863 * 2 ^ 59
def prefixEnd_5191863 : Nat := 4983230072969 + 3 ^ 40 * 5191863 * 2
def baseEnd_5191863 : Nat := 888640403764708515278521

theorem tailTrace_5191863 : CollatzResearch.WordTrace tailWord_5191863 prefixEnd_5191863 888640403764708515278521 := by
  unfold tailWord_5191863
  simp only [CollatzResearch.WordTrace]
  refine ⟨189362800389774525451748243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126241866926516350301165495 189362800389774525451748243)
  ·
    refine ⟨284044200584661788177622365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189362800389774525451748243 284044200584661788177622365)
    ·
      refine ⟨106516575219248170566608387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284044200584661788177622365 106516575219248170566608387)
      ·
        refine ⟨159774862828872255849912581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106516575219248170566608387 159774862828872255849912581)
        ·
          refine ⟨29957786780413547971858609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159774862828872255849912581 29957786780413547971858609)
          ·
            refine ⟨22468340085310160978893957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29957786780413547971858609 22468340085310160978893957)
            ·
              refine ⟨4212813765995655183542617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22468340085310160978893957 4212813765995655183542617)
              ·
                refine ⟨3159610324496741387656963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212813765995655183542617 3159610324496741387656963)
                ·
                  refine ⟨4739415486745112081485445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159610324496741387656963 4739415486745112081485445)
                  ·
                    refine ⟨888640403764708515278521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739415486745112081485445 888640403764708515278521)
                    ·
                      rfl

theorem cell23_5191863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_5191863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191863 prefixEnd_5191863 := by exact prefixLift 5191863
  have htrace : WordTrace (prefixWord ++ tailWord_5191863) baseStart_5191863 baseEnd_5191863 := by
    simpa [prefixWord, tailWord_5191863, baseEnd_5191863] using wordTrace_append hprefix tailTrace_5191863
  have hstable : (prefixWord ++ tailWord_5191863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191863).length < 2 ^ (prefixWord ++ tailWord_5191863).sum := by decide
  have hdescent : baseEnd_5191863 < baseStart_5191863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191882 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_5191882 : Nat := 118140960795 + 5191882 * 2 ^ 59
def prefixEnd_5191882 : Nat := 4983230072969 + 3 ^ 40 * 5191882 * 2
def baseEnd_5191882 : Nat := 2665930967426560971497975

theorem tailTrace_5191882 : CollatzResearch.WordTrace tailWord_5191882 prefixEnd_5191882 2665930967426560971497975 := by
  unfold tailWord_5191882
  simp only [CollatzResearch.WordTrace]
  refine ⟨47340873344176422924172475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126242328917803794464459933 47340873344176422924172475)
  ·
    refine ⟨71011310016264634386258713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47340873344176422924172475 71011310016264634386258713)
    ·
      refine ⟨53258482512198475789694035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71011310016264634386258713 53258482512198475789694035)
      ·
        refine ⟨79887723768297713684541053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53258482512198475789694035 79887723768297713684541053)
        ·
          refine ⟨29957896413111642631702895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79887723768297713684541053 29957896413111642631702895)
          ·
            refine ⟨44936844619667463947554343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29957896413111642631702895 44936844619667463947554343)
            ·
              refine ⟨67405266929501195921331515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44936844619667463947554343 67405266929501195921331515)
              ·
                refine ⟨101107900394251793881997273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67405266929501195921331515 101107900394251793881997273)
                ·
                  refine ⟨75830925295688845411497955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101107900394251793881997273 75830925295688845411497955)
                  ·
                    refine ⟨113746387943533268117246933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75830925295688845411497955 113746387943533268117246933)
                    ·
                      refine ⟨2665930967426560971497975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113746387943533268117246933 2665930967426560971497975)
                      ·
                        rfl

theorem cell23_5191882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_5191882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191882 prefixEnd_5191882 := by exact prefixLift 5191882
  have htrace : WordTrace (prefixWord ++ tailWord_5191882) baseStart_5191882 baseEnd_5191882 := by
    simpa [prefixWord, tailWord_5191882, baseEnd_5191882] using wordTrace_append hprefix tailTrace_5191882
  have hstable : (prefixWord ++ tailWord_5191882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191882).length < 2 ^ (prefixWord ++ tailWord_5191882).sum := by decide
  have hdescent : baseEnd_5191882 < baseStart_5191882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191886 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_5191886 : Nat := 118140960795 + 5191886 * 2 ^ 59
def prefixEnd_5191886 : Nat := 4983230072969 + 3 ^ 40 * 5191886 * 2
def baseEnd_5191886 : Nat := 2665933021349178955847957

theorem tailTrace_5191886 : CollatzResearch.WordTrace tailWord_5191886 prefixEnd_5191886 2665933021349178955847957 := by
  unfold tailWord_5191886
  simp only [CollatzResearch.WordTrace]
  refine ⟨23670454908586400047479439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126242426179127466919890341 23670454908586400047479439)
  ·
    refine ⟨35505682362879600071219159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23670454908586400047479439 35505682362879600071219159)
    ·
      refine ⟨53258523544319400106828739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35505682362879600071219159 53258523544319400106828739)
      ·
        refine ⟨79887785316479100160243109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53258523544319400106828739 79887785316479100160243109)
        ·
          refine ⟨14978959746839831280045583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79887785316479100160243109 14978959746839831280045583)
          ·
            refine ⟨22468439620259746920068375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14978959746839831280045583 22468439620259746920068375)
            ·
              refine ⟨33702659430389620380102563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22468439620259746920068375 33702659430389620380102563)
              ·
                refine ⟨50553989145584430570153845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33702659430389620380102563 50553989145584430570153845)
                ·
                  refine ⟨4739436482398540365951923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50553989145584430570153845 4739436482398540365951923)
                  ·
                    refine ⟨7109154723597810548927885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4739436482398540365951923 7109154723597810548927885)
                    ·
                      refine ⟨2665933021349178955847957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7109154723597810548927885 2665933021349178955847957)
                      ·
                        rfl

theorem cell23_5191886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_5191886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191886 prefixEnd_5191886 := by exact prefixLift 5191886
  have htrace : WordTrace (prefixWord ++ tailWord_5191886) baseStart_5191886 baseEnd_5191886 := by
    simpa [prefixWord, tailWord_5191886, baseEnd_5191886] using wordTrace_append hprefix tailTrace_5191886
  have hstable : (prefixWord ++ tailWord_5191886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191886).length < 2 ^ (prefixWord ++ tailWord_5191886).sum := by decide
  have hdescent : baseEnd_5191886 < baseStart_5191886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191896 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 1, 5, 2]
def baseStart_5191896 : Nat := 118140960795 + 5191896 * 2 ^ 59
def prefixEnd_5191896 : Nat := 4983230072969 + 3 ^ 40 * 5191896 * 2
def baseEnd_5191896 : Nat := 2665938156155723916722911

theorem tailTrace_5191896 : CollatzResearch.WordTrace tailWord_5191896 prefixEnd_5191896 2665938156155723916722911 := by
  unfold tailWord_5191896
  simp only [CollatzResearch.WordTrace]
  refine ⟨94682001999327486043849771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126242669332436648058466361 94682001999327486043849771)
  ·
    refine ⟨142023002998991229065774657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94682001999327486043849771 142023002998991229065774657)
    ·
      refine ⟨106517252249243421799330993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142023002998991229065774657 106517252249243421799330993)
      ·
        refine ⟨79887939186932566349498245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106517252249243421799330993 79887939186932566349498245)
        ·
          refine ⟨14978988597549856190530921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79887939186932566349498245 14978988597549856190530921)
          ·
            refine ⟨11234241448162392142898191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14978988597549856190530921 11234241448162392142898191)
            ·
              refine ⟨16851362172243588214347287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11234241448162392142898191 16851362172243588214347287)
              ·
                refine ⟨25277043258365382321520931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16851362172243588214347287 25277043258365382321520931)
                ·
                  refine ⟨37915564887548073482281397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25277043258365382321520931 37915564887548073482281397)
                  ·
                    refine ⟨3554584208207631888963881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37915564887548073482281397 3554584208207631888963881)
                    ·
                      refine ⟨2665938156155723916722911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554584208207631888963881 2665938156155723916722911)
                      ·
                        rfl

theorem cell23_5191896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_5191896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191896 prefixEnd_5191896 := by exact prefixLift 5191896
  have htrace : WordTrace (prefixWord ++ tailWord_5191896) baseStart_5191896 baseEnd_5191896 := by
    simpa [prefixWord, tailWord_5191896, baseEnd_5191896] using wordTrace_append hprefix tailTrace_5191896
  have hstable : (prefixWord ++ tailWord_5191896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191896).length < 2 ^ (prefixWord ++ tailWord_5191896).sum := by decide
  have hdescent : baseEnd_5191896 < baseStart_5191896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191929 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_5191929 : Nat := 118140960795 + 5191929 * 2 ^ 59
def prefixEnd_5191929 : Nat := 4983230072969 + 3 ^ 40 * 5191929 * 2
def baseEnd_5191929 : Nat := 2665955101017322287610259

theorem tailTrace_5191929 : CollatzResearch.WordTrace tailWord_5191929 prefixEnd_5191929 2665955101017322287610259 := by
  unfold tailWord_5191929
  simp only [CollatzResearch.WordTrace]
  refine ⟨189365207607535418723650841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126243471738356945815767227 189365207607535418723650841)
  ·
    refine ⟨142023905705651564042738131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189365207607535418723650841 142023905705651564042738131)
    ·
      refine ⟨213035858558477346064107197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142023905705651564042738131 213035858558477346064107197)
      ·
        refine ⟨79888446959429004774040199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213035858558477346064107197 79888446959429004774040199)
        ·
          refine ⟨119832670439143507161060299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79888446959429004774040199 119832670439143507161060299)
          ·
            refine ⟨179749005658715260741590449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119832670439143507161060299 179749005658715260741590449)
            ·
              refine ⟨134811754244036445556192837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179749005658715260741590449 134811754244036445556192837)
              ·
                refine ⟨25277203920756833541786157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134811754244036445556192837 25277203920756833541786157)
                ·
                  refine ⟨9478951470283812578169809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25277203920756833541786157 9478951470283812578169809)
                  ·
                    refine ⟨7109213602712859433627357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9478951470283812578169809 7109213602712859433627357)
                    ·
                      refine ⟨2665955101017322287610259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7109213602712859433627357 2665955101017322287610259)
                      ·
                        rfl

theorem cell23_5191929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_5191929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191929 prefixEnd_5191929 := by exact prefixLift 5191929
  have htrace : WordTrace (prefixWord ++ tailWord_5191929) baseStart_5191929 baseEnd_5191929 := by
    simpa [prefixWord, tailWord_5191929, baseEnd_5191929] using wordTrace_append hprefix tailTrace_5191929
  have hstable : (prefixWord ++ tailWord_5191929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191929).length < 2 ^ (prefixWord ++ tailWord_5191929).sum := by decide
  have hdescent : baseEnd_5191929 < baseStart_5191929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191946 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_5191946 : Nat := 118140960795 + 5191946 * 2 ^ 59
def prefixEnd_5191946 : Nat := 4983230072969 + 3 ^ 40 * 5191946 * 2
def baseEnd_5191946 : Nat := 2665963830188448721097681

theorem tailTrace_5191946 : CollatzResearch.WordTrace tailWord_5191946 prefixEnd_5191946 2665963830188448721097681 := by
  unfold tailWord_5191946
  simp only [CollatzResearch.WordTrace]
  refine ⟨47341456912118457656754923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126243885098982553751346461 47341456912118457656754923)
  ·
    refine ⟨71012185368177686485132385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47341456912118457656754923 71012185368177686485132385)
    ·
      refine ⟨53259139026133264863849289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71012185368177686485132385 53259139026133264863849289)
      ·
        refine ⟨39944354269599948647886967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53259139026133264863849289 39944354269599948647886967)
        ·
          refine ⟨59916531404399922971830451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39944354269599948647886967 59916531404399922971830451)
          ·
            refine ⟨89874797106599884457745677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59916531404399922971830451 89874797106599884457745677)
            ·
              refine ⟨33703048914974956671654629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89874797106599884457745677 33703048914974956671654629)
              ·
                refine ⟨6319321671557804375935243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33703048914974956671654629 6319321671557804375935243)
                ·
                  refine ⟨9478982507336706563902865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6319321671557804375935243 9478982507336706563902865)
                  ·
                    refine ⟨7109236880502529922927149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9478982507336706563902865 7109236880502529922927149)
                    ·
                      refine ⟨2665963830188448721097681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7109236880502529922927149 2665963830188448721097681)
                      ·
                        rfl

theorem cell23_5191946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_5191946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191946 prefixEnd_5191946 := by exact prefixLift 5191946
  have htrace : WordTrace (prefixWord ++ tailWord_5191946) baseStart_5191946 baseEnd_5191946 := by
    simpa [prefixWord, tailWord_5191946, baseEnd_5191946] using wordTrace_append hprefix tailTrace_5191946
  have hstable : (prefixWord ++ tailWord_5191946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191946).length < 2 ^ (prefixWord ++ tailWord_5191946).sum := by decide
  have hdescent : baseEnd_5191946 < baseStart_5191946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5191966 : List Nat := [4, 3, 2, 1, 1, 1, 11]
def baseStart_5191966 : Nat := 118140960795 + 5191966 * 2 ^ 59
def prefixEnd_5191966 : Nat := 4983230072969 + 3 ^ 40 * 5191966 * 2
def baseEnd_5191966 : Nat := 32913260491377020282069

theorem tailTrace_5191966 : CollatzResearch.WordTrace tailWord_5191966 prefixEnd_5191966 32913260491377020282069 := by
  unfold tailWord_5191966
  simp only [CollatzResearch.WordTrace]
  refine ⟨23670819638550171755343469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126244371405600916028498501 23670819638550171755343469)
  ·
    refine ⟨8876557364456314408253801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23670819638550171755343469 8876557364456314408253801)
    ·
      refine ⟨6657418023342235806190351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8876557364456314408253801 6657418023342235806190351)
      ·
        refine ⟨9986127035013353709285527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6657418023342235806190351 9986127035013353709285527)
        ·
          refine ⟨14979190552520030563928291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9986127035013353709285527 14979190552520030563928291)
          ·
            refine ⟨22468785828780045845892437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14979190552520030563928291 22468785828780045845892437)
            ·
              refine ⟨32913260491377020282069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22468785828780045845892437 32913260491377020282069)
              ·
                rfl

theorem cell23_5191966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 11].length) (baseStart_5191966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5191966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5191966 prefixEnd_5191966 := by exact prefixLift 5191966
  have htrace : WordTrace (prefixWord ++ tailWord_5191966) baseStart_5191966 baseEnd_5191966 := by
    simpa [prefixWord, tailWord_5191966, baseEnd_5191966] using wordTrace_append hprefix tailTrace_5191966
  have hstable : (prefixWord ++ tailWord_5191966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5191966).length < 2 ^ (prefixWord ++ tailWord_5191966).sum := by decide
  have hdescent : baseEnd_5191966 < baseStart_5191966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5191966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192003 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 1, 3, 2]
def baseStart_5192003 : Nat := 118140960795 + 5192003 * 2 ^ 59
def prefixEnd_5192003 : Nat := 4983230072969 + 3 ^ 40 * 5192003 * 2
def baseEnd_5192003 : Nat := 2665993098585754998084919

theorem tailTrace_5192003 : CollatzResearch.WordTrace tailWord_5192003 prefixEnd_5192003 2665993098585754998084919 := by
  unfold tailWord_5192003
  simp only [CollatzResearch.WordTrace]
  refine ⟨189367906609267329361844663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126245271072844886241229775 189367906609267329361844663)
  ·
    refine ⟨284051859913900994042766995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189367906609267329361844663 284051859913900994042766995)
    ·
      refine ⟨426077789870851491064150493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284051859913900994042766995 426077789870851491064150493)
      ·
        refine ⟨159779171201569309149056435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426077789870851491064150493 159779171201569309149056435)
        ·
          refine ⟨239668756802353963723584653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159779171201569309149056435 239668756802353963723584653)
          ·
            refine ⟨89875783800882736396344245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239668756802353963723584653 89875783800882736396344245)
            ·
              refine ⟨8425854731332756537157273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89875783800882736396344245 8425854731332756537157273)
              ·
                refine ⟨6319391048499567402867955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8425854731332756537157273 6319391048499567402867955)
                ·
                  refine ⟨9479086572749351104301933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6319391048499567402867955 9479086572749351104301933)
                  ·
                    refine ⟨3554657464781006664113225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9479086572749351104301933 3554657464781006664113225)
                    ·
                      refine ⟨2665993098585754998084919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554657464781006664113225 2665993098585754998084919)
                      ·
                        rfl

theorem cell23_5192003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_5192003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192003 prefixEnd_5192003 := by exact prefixLift 5192003
  have htrace : WordTrace (prefixWord ++ tailWord_5192003) baseStart_5192003 baseEnd_5192003 := by
    simpa [prefixWord, tailWord_5192003, baseEnd_5192003] using wordTrace_append hprefix tailTrace_5192003
  have hstable : (prefixWord ++ tailWord_5192003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192003).length < 2 ^ (prefixWord ++ tailWord_5192003).sum := by decide
  have hdescent : baseEnd_5192003 < baseStart_5192003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192016 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 3, 4, 2]
def baseStart_5192016 : Nat := 118140960795 + 5192016 * 2 ^ 59
def prefixEnd_5192016 : Nat := 4983230072969 + 3 ^ 40 * 5192016 * 2
def baseEnd_5192016 : Nat := 2665999773834263447222359

theorem tailTrace_5192016 : CollatzResearch.WordTrace tailWord_5192016 prefixEnd_5192016 2665999773834263447222359 := by
  unfold tailWord_5192016
  simp only [CollatzResearch.WordTrace]
  refine ⟨94684190379110116291033951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126245587172146821721378601 94684190379110116291033951)
  ·
    refine ⟨142026285568665174436550927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94684190379110116291033951 142026285568665174436550927)
    ·
      refine ⟨213039428352997761654826391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142026285568665174436550927 213039428352997761654826391)
      ·
        refine ⟨319559142529496642482239587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213039428352997761654826391 319559142529496642482239587)
        ·
          refine ⟨479338713794244963723359381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319559142529496642482239587 479338713794244963723359381)
          ·
            refine ⟨22469002209105232674532471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 479338713794244963723359381 22469002209105232674532471)
            ·
              refine ⟨33703503313657849011798707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22469002209105232674532471 33703503313657849011798707)
              ·
                refine ⟨50555254970486773517698061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33703503313657849011798707 50555254970486773517698061)
                ·
                  refine ⟨18958220613932540069136773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50555254970486773517698061 18958220613932540069136773)
                  ·
                    refine ⟨3554666365112351262963145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18958220613932540069136773 3554666365112351262963145)
                    ·
                      refine ⟨2665999773834263447222359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554666365112351262963145 2665999773834263447222359)
                      ·
                        rfl

theorem cell23_5192016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 4, 2].length) (baseStart_5192016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192016 prefixEnd_5192016 := by exact prefixLift 5192016
  have htrace : WordTrace (prefixWord ++ tailWord_5192016) baseStart_5192016 baseEnd_5192016 := by
    simpa [prefixWord, tailWord_5192016, baseEnd_5192016] using wordTrace_append hprefix tailTrace_5192016
  have hstable : (prefixWord ++ tailWord_5192016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192016).length < 2 ^ (prefixWord ++ tailWord_5192016).sum := by decide
  have hdescent : baseEnd_5192016 < baseStart_5192016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192028 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5192028 : Nat := 118140960795 + 5192028 * 2 ^ 59
def prefixEnd_5192028 : Nat := 4983230072969 + 3 ^ 40 * 5192028 * 2
def baseEnd_5192028 : Nat := 2666005935602117400272305

theorem tailTrace_5192028 : CollatzResearch.WordTrace tailWord_5192028 prefixEnd_5192028 2666005935602117400272305 := by
  unfold tailWord_5192028
  simp only [CollatzResearch.WordTrace]
  refine ⟨94684409217088379315752369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126245878956117839087669825 94684409217088379315752369)
  ·
    refine ⟨71013306912816284486814277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94684409217088379315752369 71013306912816284486814277)
    ·
      refine ⟨13314995046153053341277677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71013306912816284486814277 13314995046153053341277677)
      ·
        refine ⟨4993123142307395002979129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13314995046153053341277677 4993123142307395002979129)
        ·
          refine ⟨3744842356730546252234347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4993123142307395002979129 3744842356730546252234347)
          ·
            refine ⟨5617263535095819378351521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744842356730546252234347 5617263535095819378351521)
            ·
              refine ⟨4212947651321864533763641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617263535095819378351521 4212947651321864533763641)
              ·
                refine ⟨3159710738491398400322731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212947651321864533763641 3159710738491398400322731)
                ·
                  refine ⟨4739566107737097600484097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159710738491398400322731 4739566107737097600484097)
                  ·
                    refine ⟨3554674580802823200363073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4739566107737097600484097 3554674580802823200363073)
                    ·
                      refine ⟨2666005935602117400272305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554674580802823200363073 2666005935602117400272305)
                      ·
                        rfl

theorem cell23_5192028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5192028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192028 prefixEnd_5192028 := by exact prefixLift 5192028
  have htrace : WordTrace (prefixWord ++ tailWord_5192028) baseStart_5192028 baseEnd_5192028 := by
    simpa [prefixWord, tailWord_5192028, baseEnd_5192028] using wordTrace_append hprefix tailTrace_5192028
  have hstable : (prefixWord ++ tailWord_5192028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192028).length < 2 ^ (prefixWord ++ tailWord_5192028).sum := by decide
  have hdescent : baseEnd_5192028 < baseStart_5192028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192050 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_5192050 : Nat := 118140960795 + 5192050 * 2 ^ 59
def prefixEnd_5192050 : Nat := 4983230072969 + 3 ^ 40 * 5192050 * 2
def baseEnd_5192050 : Nat := 2666017232176516314197203

theorem tailTrace_5192050 : CollatzResearch.WordTrace tailWord_5192050 prefixEnd_5192050 2666017232176516314197203 := by
  unfold tailWord_5192050
  simp only [CollatzResearch.WordTrace]
  refine ⟨47342405210024264097201401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126246413893398037592537069 47342405210024264097201401)
  ·
    refine ⟨35506803907518198072901051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47342405210024264097201401 35506803907518198072901051)
    ·
      refine ⟨53260205861277297109351577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35506803907518198072901051 53260205861277297109351577)
      ·
        refine ⟨39945154395957972832013683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53260205861277297109351577 39945154395957972832013683)
        ·
          refine ⟨59917731593936959248020525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39945154395957972832013683 59917731593936959248020525)
          ·
            refine ⟨22469149347726359718007697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59917731593936959248020525 22469149347726359718007697)
            ·
              refine ⟨16851862010794769788505773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22469149347726359718007697 16851862010794769788505773)
              ·
                refine ⟨6319448254048038670689665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16851862010794769788505773 6319448254048038670689665)
                ·
                  refine ⟨4739586190536029003017249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6319448254048038670689665 4739586190536029003017249)
                  ·
                    refine ⟨3554689642902021752262937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4739586190536029003017249 3554689642902021752262937)
                    ·
                      refine ⟨2666017232176516314197203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554689642902021752262937 2666017232176516314197203)
                      ·
                        rfl

theorem cell23_5192050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_5192050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192050 prefixEnd_5192050 := by exact prefixLift 5192050
  have htrace : WordTrace (prefixWord ++ tailWord_5192050) baseStart_5192050 baseEnd_5192050 := by
    simpa [prefixWord, tailWord_5192050, baseEnd_5192050] using wordTrace_append hprefix tailTrace_5192050
  have hstable : (prefixWord ++ tailWord_5192050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192050).length < 2 ^ (prefixWord ++ tailWord_5192050).sum := by decide
  have hdescent : baseEnd_5192050 < baseStart_5192050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192073 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 5]
def baseStart_5192073 : Nat := 118140960795 + 5192073 * 2 ^ 59
def prefixEnd_5192073 : Nat := 4983230072969 + 3 ^ 40 * 5192073 * 2
def baseEnd_5192073 : Nat := 296225449136841080467733

theorem tailTrace_5192073 : CollatzResearch.WordTrace tailWord_5192073 prefixEnd_5192073 296225449136841080467733 := by
  unfold tailWord_5192073
  simp only [CollatzResearch.WordTrace]
  refine ⟨189370459719013731316892873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126246973146009154211261915 189370459719013731316892873)
  ·
    refine ⟨142027844789260298487669655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189370459719013731316892873 142027844789260298487669655)
    ·
      refine ⟨213041767183890447731504483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142027844789260298487669655 213041767183890447731504483)
      ·
        refine ⟨319562650775835671597256725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213041767183890447731504483 319562650775835671597256725)
        ·
          refine ⟨14979499255117297106121409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 319562650775835671597256725 14979499255117297106121409)
          ·
            refine ⟨11234624441337972829591057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14979499255117297106121409 11234624441337972829591057)
            ·
              refine ⟨8425968331003479622193293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11234624441337972829591057 8425968331003479622193293)
              ·
                refine ⟨3159738124126304858322485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8425968331003479622193293 3159738124126304858322485)
                ·
                  refine ⟨296225449136841080467733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3159738124126304858322485 296225449136841080467733)
                  ·
                    rfl

theorem cell23_5192073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 5].length) (baseStart_5192073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192073 prefixEnd_5192073 := by exact prefixLift 5192073
  have htrace : WordTrace (prefixWord ++ tailWord_5192073) baseStart_5192073 baseEnd_5192073 := by
    simpa [prefixWord, tailWord_5192073, baseEnd_5192073] using wordTrace_append hprefix tailTrace_5192073
  have hstable : (prefixWord ++ tailWord_5192073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192073).length < 2 ^ (prefixWord ++ tailWord_5192073).sum := by decide
  have hdescent : baseEnd_5192073 < baseStart_5192073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192084 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_5192084 : Nat := 118140960795 + 5192084 * 2 ^ 59
def prefixEnd_5192084 : Nat := 4983230072969 + 3 ^ 40 * 5192084 * 2
def baseEnd_5192084 : Nat := 2666034690518769181172047

theorem tailTrace_5192084 : CollatzResearch.WordTrace tailWord_5192084 prefixEnd_5192084 2666034690518769181172047 := by
  unfold tailWord_5192084
  simp only [CollatzResearch.WordTrace]
  refine ⟨94685430460986940097771653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126247240614649253463695537 94685430460986940097771653)
  ·
    refine ⟨17753518211435051268332185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94685430460986940097771653 17753518211435051268332185)
    ·
      refine ⟨13315138658576288451249139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17753518211435051268332185 13315138658576288451249139)
      ·
        refine ⟨19972707987864432676873709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13315138658576288451249139 19972707987864432676873709)
        ·
          refine ⟨7489765495449162253827641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19972707987864432676873709 7489765495449162253827641)
          ·
            refine ⟨5617324121586871690370731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7489765495449162253827641 5617324121586871690370731)
            ·
              refine ⟨8425986182380307535556097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617324121586871690370731 8425986182380307535556097)
              ·
                refine ⟨6319489636785230651667073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8425986182380307535556097 6319489636785230651667073)
                ·
                  refine ⟨4739617227588922988750305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6319489636785230651667073 4739617227588922988750305)
                  ·
                    refine ⟨3554712920691692241562729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4739617227588922988750305 3554712920691692241562729)
                    ·
                      refine ⟨2666034690518769181172047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554712920691692241562729 2666034690518769181172047)
                      ·
                        rfl

theorem cell23_5192084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_5192084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192084 prefixEnd_5192084 := by exact prefixLift 5192084
  have htrace : WordTrace (prefixWord ++ tailWord_5192084) baseStart_5192084 baseEnd_5192084 := by
    simpa [prefixWord, tailWord_5192084, baseEnd_5192084] using wordTrace_append hprefix tailTrace_5192084
  have hstable : (prefixWord ++ tailWord_5192084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192084).length < 2 ^ (prefixWord ++ tailWord_5192084).sum := by decide
  have hdescent : baseEnd_5192084 < baseStart_5192084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192163 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 6]
def baseStart_5192163 : Nat := 118140960795 + 5192163 * 2 ^ 59
def prefixEnd_5192163 : Nat := 4983230072969 + 3 ^ 40 * 5192163 * 2
def baseEnd_5192163 : Nat := 296230583943386041342687

theorem tailTrace_5192163 : CollatzResearch.WordTrace tailWord_5192163 prefixEnd_5192163 296230583943386041342687 := by
  unfold tailWord_5192163
  simp only [CollatzResearch.WordTrace]
  refine ⟨189373742288687676687669143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126249161525791784458446095 189373742288687676687669143)
  ·
    refine ⟨284060613433031515031503715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189373742288687676687669143 284060613433031515031503715)
    ·
      refine ⟨426090920149547272547255573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284060613433031515031503715 426090920149547272547255573)
      ·
        refine ⟨19973011882010028400652605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 426090920149547272547255573 19973011882010028400652605)
        ·
          refine ⟨7489879455753760650244727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19973011882010028400652605 7489879455753760650244727)
          ·
            refine ⟨11234819183630640975367091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7489879455753760650244727 11234819183630640975367091)
            ·
              refine ⟨16852228775445961463050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11234819183630640975367091 16852228775445961463050637)
              ·
                refine ⟨6319585790792235548643989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16852228775445961463050637 6319585790792235548643989)
                ·
                  refine ⟨296230583943386041342687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6319585790792235548643989 296230583943386041342687)
                  ·
                    rfl

theorem cell23_5192163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 6].length) (baseStart_5192163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192163 prefixEnd_5192163 := by exact prefixLift 5192163
  have htrace : WordTrace (prefixWord ++ tailWord_5192163) baseStart_5192163 baseEnd_5192163 := by
    simpa [prefixWord, tailWord_5192163, baseEnd_5192163] using wordTrace_append hprefix tailTrace_5192163
  have hstable : (prefixWord ++ tailWord_5192163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192163).length < 2 ^ (prefixWord ++ tailWord_5192163).sum := by decide
  have hdescent : baseEnd_5192163 < baseStart_5192163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192169 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_5192169 : Nat := 118140960795 + 5192169 * 2 ^ 59
def prefixEnd_5192169 : Nat := 4983230072969 + 3 ^ 40 * 5192169 * 2
def baseEnd_5192169 : Nat := 2666078336374401348609155

theorem tailTrace_5192169 : CollatzResearch.WordTrace tailWord_5192169 prefixEnd_5192169 2666078336374401348609155 := by
  unfold tailWord_5192169
  simp only [CollatzResearch.WordTrace]
  refine ⟨189373961126665939712387561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126249307417777293141591707 189373961126665939712387561)
  ·
    refine ⟨142030470844999454784290671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189373961126665939712387561 142030470844999454784290671)
    ·
      refine ⟨213045706267499182176436007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142030470844999454784290671 213045706267499182176436007)
      ·
        refine ⟨319568559401248773264654011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213045706267499182176436007 319568559401248773264654011)
        ·
          refine ⟨479352839101873159896981017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319568559401248773264654011 479352839101873159896981017)
          ·
            refine ⟨359514629326404869922735763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479352839101873159896981017 359514629326404869922735763)
            ·
              refine ⟨539271943989607304884103645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359514629326404869922735763 539271943989607304884103645)
              ·
                refine ⟨202226978996102739331538867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 539271943989607304884103645 202226978996102739331538867)
                ·
                  refine ⟨303340468494154108997308301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202226978996102739331538867 303340468494154108997308301)
                  ·
                    refine ⟨113752675685307790873990613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303340468494154108997308301 113752675685307790873990613)
                    ·
                      refine ⟨2666078336374401348609155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113752675685307790873990613 2666078336374401348609155)
                      ·
                        rfl

theorem cell23_5192169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_5192169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192169 prefixEnd_5192169 := by exact prefixLift 5192169
  have htrace : WordTrace (prefixWord ++ tailWord_5192169) baseStart_5192169 baseEnd_5192169 := by
    simpa [prefixWord, tailWord_5192169, baseEnd_5192169] using wordTrace_append hprefix tailTrace_5192169
  have hstable : (prefixWord ++ tailWord_5192169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192169).length < 2 ^ (prefixWord ++ tailWord_5192169).sum := by decide
  have hdescent : baseEnd_5192169 < baseStart_5192169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192176 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_5192176 : Nat := 118140960795 + 5192176 * 2 ^ 59
def prefixEnd_5192176 : Nat := 4983230072969 + 3 ^ 40 * 5192176 * 2
def baseEnd_5192176 : Nat := 888693976912994273740541

theorem tailTrace_5192176 : CollatzResearch.WordTrace tailWord_5192176 prefixEnd_5192176 888693976912994273740541 := by
  unfold tailWord_5192176
  simp only [CollatzResearch.WordTrace]
  refine ⟨94687108218820289953946191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126249477625093719938594921 94687108218820289953946191)
  ·
    refine ⟨142030662328230434930919287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94687108218820289953946191 142030662328230434930919287)
    ·
      refine ⟨213045993492345652396378931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142030662328230434930919287 213045993492345652396378931)
      ·
        refine ⟨319568990238518478594568397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213045993492345652396378931 319568990238518478594568397)
        ·
          refine ⟨119838371339444429472963149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319568990238518478594568397 119838371339444429472963149)
          ·
            refine ⟨44939389252291661052361181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119838371339444429472963149 44939389252291661052361181)
            ·
              refine ⟨16852270969609372894635443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44939389252291661052361181 16852270969609372894635443)
              ·
                refine ⟨25278406454414059341953165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16852270969609372894635443 25278406454414059341953165)
                ·
                  refine ⟨9479402420405272253232437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25278406454414059341953165 9479402420405272253232437)
                  ·
                    refine ⟨888693976912994273740541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9479402420405272253232437 888693976912994273740541)
                    ·
                      rfl

theorem cell23_5192176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_5192176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192176 prefixEnd_5192176 := by exact prefixLift 5192176
  have htrace : WordTrace (prefixWord ++ tailWord_5192176) baseStart_5192176 baseEnd_5192176 := by
    simpa [prefixWord, tailWord_5192176, baseEnd_5192176] using wordTrace_append hprefix tailTrace_5192176
  have hstable : (prefixWord ++ tailWord_5192176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192176).length < 2 ^ (prefixWord ++ tailWord_5192176).sum := by decide
  have hdescent : baseEnd_5192176 < baseStart_5192176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192250 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3]
def baseStart_5192250 : Nat := 118140960795 + 5192250 * 2 ^ 59
def prefixEnd_5192250 : Nat := 4983230072969 + 3 ^ 40 * 5192250 * 2
def baseEnd_5192250 : Nat := 2666119928307415531696283

theorem tailTrace_5192250 : CollatzResearch.WordTrace tailWord_5192250 prefixEnd_5192250 2666119928307415531696283 := by
  unfold tailWord_5192250
  simp only [CollatzResearch.WordTrace]
  refine ⟨47344228859843122636521551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126251276959581660364057469 47344228859843122636521551)
  ·
    refine ⟨71016343289764683954782327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47344228859843122636521551 71016343289764683954782327)
    ·
      refine ⟨106524514934647025932173491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71016343289764683954782327 106524514934647025932173491)
      ·
        refine ⟨159786772401970538898260237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106524514934647025932173491 159786772401970538898260237)
        ·
          refine ⟨59920039650738952086847589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159786772401970538898260237 59920039650738952086847589)
          ·
            refine ⟨11235007434513553516283923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59920039650738952086847589 11235007434513553516283923)
            ·
              refine ⟨16852511151770330274425885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11235007434513553516283923 16852511151770330274425885)
              ·
                refine ⟨6319691681913873852909707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16852511151770330274425885 6319691681913873852909707)
                ·
                  refine ⟨9479537522870810779364561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6319691681913873852909707 9479537522870810779364561)
                  ·
                    refine ⟨7109653142153108084523421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9479537522870810779364561 7109653142153108084523421)
                    ·
                      refine ⟨2666119928307415531696283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7109653142153108084523421 2666119928307415531696283)
                      ·
                        rfl

theorem cell23_5192250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_5192250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192250 prefixEnd_5192250 := by exact prefixLift 5192250
  have htrace : WordTrace (prefixWord ++ tailWord_5192250) baseStart_5192250 baseEnd_5192250 := by
    simpa [prefixWord, tailWord_5192250, baseEnd_5192250] using wordTrace_append hprefix tailTrace_5192250
  have hstable : (prefixWord ++ tailWord_5192250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192250).length < 2 ^ (prefixWord ++ tailWord_5192250).sum := by decide
  have hdescent : baseEnd_5192250 < baseStart_5192250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192257 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5192257 : Nat := 118140960795 + 5192257 * 2 ^ 59
def prefixEnd_5192257 : Nat := 4983230072969 + 3 ^ 40 * 5192257 * 2
def baseEnd_5192257 : Nat := 888707840890665668102917

theorem tailTrace_5192257 : CollatzResearch.WordTrace tailWord_5192257 prefixEnd_5192257 888707840890665668102917 := by
  unfold tailWord_5192257
  simp only [CollatzResearch.WordTrace]
  refine ⟨189377170750347130741591025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126251447166898087161060683 189377170750347130741591025)
  ·
    refine ⟨142032878062760348056193269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189377170750347130741591025 142032878062760348056193269)
    ·
      refine ⟨13315582318383782630268119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142032878062760348056193269 13315582318383782630268119)
      ·
        refine ⟨19973373477575673945402179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13315582318383782630268119 19973373477575673945402179)
        ·
          refine ⟨29960060216363510918103269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19973373477575673945402179 29960060216363510918103269)
          ·
            refine ⟨5617511290568158297144363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29960060216363510918103269 5617511290568158297144363)
            ·
              refine ⟨8426266935852237445716545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617511290568158297144363 8426266935852237445716545)
              ·
                refine ⟨6319700201889178084287409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8426266935852237445716545 6319700201889178084287409)
                ·
                  refine ⟨4739775151416883563215557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6319700201889178084287409 4739775151416883563215557)
                  ·
                    refine ⟨888707840890665668102917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739775151416883563215557 888707840890665668102917)
                    ·
                      rfl

theorem cell23_5192257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5192257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192257 prefixEnd_5192257 := by exact prefixLift 5192257
  have htrace : WordTrace (prefixWord ++ tailWord_5192257) baseStart_5192257 baseEnd_5192257 := by
    simpa [prefixWord, tailWord_5192257, baseEnd_5192257] using wordTrace_append hprefix tailTrace_5192257
  have hstable : (prefixWord ++ tailWord_5192257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192257).length < 2 ^ (prefixWord ++ tailWord_5192257).sum := by decide
  have hdescent : baseEnd_5192257 < baseStart_5192257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192280 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_5192280 : Nat := 118140960795 + 5192280 * 2 ^ 59
def prefixEnd_5192280 : Nat := 4983230072969 + 3 ^ 40 * 5192280 * 2
def baseEnd_5192280 : Nat := 2666135332727050414321145

theorem tailTrace_5192280 : CollatzResearch.WordTrace tailWord_5192280 prefixEnd_5192280 2666135332727050414321145 := by
  unfold tailWord_5192280
  simp only [CollatzResearch.WordTrace]
  refine ⟨94689004814631902834839147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126252006419509203779785529 94689004814631902834839147)
  ·
    refine ⟨142033507221947854252258721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94689004814631902834839147 142033507221947854252258721)
    ·
      refine ⟨106525130416460890689194041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142033507221947854252258721 106525130416460890689194041)
      ·
        refine ⟨79893847812345668016895531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106525130416460890689194041 79893847812345668016895531)
        ·
          refine ⟨119840771718518502025343297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79893847812345668016895531 119840771718518502025343297)
          ·
            refine ⟨89880578788888876519007473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119840771718518502025343297 89880578788888876519007473)
            ·
              refine ⟨67410434091666657389255605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89880578788888876519007473 67410434091666657389255605)
              ·
                refine ⟨6319728196093749130242713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67410434091666657389255605 6319728196093749130242713)
                ·
                  refine ⟨4739796147070311847682035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6319728196093749130242713 4739796147070311847682035)
                  ·
                    refine ⟨7109694220605467771523053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4739796147070311847682035 7109694220605467771523053)
                    ·
                      refine ⟨2666135332727050414321145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7109694220605467771523053 2666135332727050414321145)
                      ·
                        rfl

theorem cell23_5192280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_5192280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192280 prefixEnd_5192280 := by exact prefixLift 5192280
  have htrace : WordTrace (prefixWord ++ tailWord_5192280) baseStart_5192280 baseEnd_5192280 := by
    simpa [prefixWord, tailWord_5192280, baseEnd_5192280] using wordTrace_append hprefix tailTrace_5192280
  have hstable : (prefixWord ++ tailWord_5192280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192280).length < 2 ^ (prefixWord ++ tailWord_5192280).sum := by decide
  have hdescent : baseEnd_5192280 < baseStart_5192280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192340 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5192340 : Nat := 118140960795 + 5192340 * 2 ^ 59
def prefixEnd_5192340 : Nat := 4983230072969 + 3 ^ 40 * 5192340 * 2
def baseEnd_5192340 : Nat := 2666166141566320179570869

theorem tailTrace_5192340 : CollatzResearch.WordTrace tailWord_5192340 prefixEnd_5192340 2666166141566320179570869 := by
  unfold tailWord_5192340
  simp only [CollatzResearch.WordTrace]
  refine ⟨94690099004523217958431237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126253465339364290611241649 94690099004523217958431237)
  ·
    refine ⟨17754393563348103367205857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94690099004523217958431237 17754393563348103367205857)
    ·
      refine ⟨13315795172511077525404393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17754393563348103367205857 13315795172511077525404393)
      ·
        refine ⟨9986846379383308144053295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13315795172511077525404393 9986846379383308144053295)
        ·
          refine ⟨14980269569074962216079943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9986846379383308144053295 14980269569074962216079943)
          ·
            refine ⟨22470404353612443324119915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14980269569074962216079943 22470404353612443324119915)
            ·
              refine ⟨33705606530418664986179873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22470404353612443324119915 33705606530418664986179873)
              ·
                refine ⟨25279204897813998739634905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33705606530418664986179873 25279204897813998739634905)
                ·
                  refine ⟨18959403673360499054726179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25279204897813998739634905 18959403673360499054726179)
                  ·
                    refine ⟨28439105510040748582089269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18959403673360499054726179 28439105510040748582089269)
                    ·
                      refine ⟨2666166141566320179570869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28439105510040748582089269 2666166141566320179570869)
                      ·
                        rfl

theorem cell23_5192340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5192340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192340 prefixEnd_5192340 := by exact prefixLift 5192340
  have htrace : WordTrace (prefixWord ++ tailWord_5192340) baseStart_5192340 baseEnd_5192340 := by
    simpa [prefixWord, tailWord_5192340, baseEnd_5192340] using wordTrace_append hprefix tailTrace_5192340
  have hstable : (prefixWord ++ tailWord_5192340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192340).length < 2 ^ (prefixWord ++ tailWord_5192340).sum := by decide
  have hdescent : baseEnd_5192340 < baseStart_5192340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192380 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_5192380 : Nat := 118140960795 + 5192380 * 2 ^ 59
def prefixEnd_5192380 : Nat := 4983230072969 + 3 ^ 40 * 5192380 * 2
def baseEnd_5192380 : Nat := 2666186680792500023070685

theorem tailTrace_5192380 : CollatzResearch.WordTrace tailWord_5192380 prefixEnd_5192380 2666186680792500023070685 := by
  unfold tailWord_5192380
  simp only [CollatzResearch.WordTrace]
  refine ⟨94690828464450761374159297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126254437952601015165545729 94690828464450761374159297)
  ·
    refine ⟨71018121348338071030619473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94690828464450761374159297 71018121348338071030619473)
    ·
      refine ⟨53263591011253553272964605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71018121348338071030619473 53263591011253553272964605)
      ·
        refine ⟨19973846629220082477361727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53263591011253553272964605 19973846629220082477361727)
        ·
          refine ⟨29960769943830123716042591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19973846629220082477361727 29960769943830123716042591)
          ·
            refine ⟨44941154915745185574063887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29960769943830123716042591 44941154915745185574063887)
            ·
              refine ⟨67411732373617778361095831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44941154915745185574063887 67411732373617778361095831)
              ·
                refine ⟨101117598560426667541643747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67411732373617778361095831 101117598560426667541643747)
                ·
                  refine ⟨151676397840640001312465621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101117598560426667541643747 151676397840640001312465621)
                  ·
                    refine ⟨3554915574390000030760913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151676397840640001312465621 3554915574390000030760913)
                    ·
                      refine ⟨2666186680792500023070685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554915574390000030760913 2666186680792500023070685)
                      ·
                        rfl

theorem cell23_5192380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_5192380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192380 prefixEnd_5192380 := by exact prefixLift 5192380
  have htrace : WordTrace (prefixWord ++ tailWord_5192380) baseStart_5192380 baseEnd_5192380 := by
    simpa [prefixWord, tailWord_5192380, baseEnd_5192380] using wordTrace_append hprefix tailTrace_5192380
  have hstable : (prefixWord ++ tailWord_5192380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192380).length < 2 ^ (prefixWord ++ tailWord_5192380).sum := by decide
  have hdescent : baseEnd_5192380 < baseStart_5192380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192383 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_5192383 : Nat := 118140960795 + 5192383 * 2 ^ 59
def prefixEnd_5192383 : Nat := 4983230072969 + 3 ^ 40 * 5192383 * 2
def baseEnd_5192383 : Nat := 2666188221234463511333171

theorem tailTrace_5192383 : CollatzResearch.WordTrace tailWord_5192383 prefixEnd_5192383 2666188221234463511333171 := by
  unfold tailWord_5192383
  simp only [CollatzResearch.WordTrace]
  refine ⟨189381766347890654260677803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126254510898593769507118535 189381766347890654260677803)
  ·
    refine ⟨284072649521835981391016705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189381766347890654260677803 284072649521835981391016705)
    ·
      refine ⟨213054487141376986043262529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284072649521835981391016705 213054487141376986043262529)
      ·
        refine ⟨159790865356032739532446897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213054487141376986043262529 159790865356032739532446897)
        ·
          refine ⟨119843149017024554649335173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159790865356032739532446897 119843149017024554649335173)
          ·
            refine ⟨22470590440692103996750345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119843149017024554649335173 22470590440692103996750345)
            ·
              refine ⟨16852942830519077997562759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22470590440692103996750345 16852942830519077997562759)
              ·
                refine ⟨25279414245778616996344139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16852942830519077997562759 25279414245778616996344139)
                ·
                  refine ⟨37919121368667925494516209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25279414245778616996344139 37919121368667925494516209)
                  ·
                    refine ⟨28439341026500944120887157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37919121368667925494516209 28439341026500944120887157)
                    ·
                      refine ⟨2666188221234463511333171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28439341026500944120887157 2666188221234463511333171)
                      ·
                        rfl

theorem cell23_5192383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_5192383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192383 prefixEnd_5192383 := by exact prefixLift 5192383
  have htrace : WordTrace (prefixWord ++ tailWord_5192383) baseStart_5192383 baseEnd_5192383 := by
    simpa [prefixWord, tailWord_5192383, baseEnd_5192383] using wordTrace_append hprefix tailTrace_5192383
  have hstable : (prefixWord ++ tailWord_5192383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192383).length < 2 ^ (prefixWord ++ tailWord_5192383).sum := by decide
  have hdescent : baseEnd_5192383 < baseStart_5192383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192410 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2]
def baseStart_5192410 : Nat := 118140960795 + 5192410 * 2 ^ 59
def prefixEnd_5192410 : Nat := 4983230072969 + 3 ^ 40 * 5192410 * 2
def baseEnd_5192410 : Nat := 2666202085212134905695547

theorem tailTrace_5192410 : CollatzResearch.WordTrace tailWord_5192410 prefixEnd_5192410 2666202085212134905695547 := by
  unfold tailWord_5192410
  simp only [CollatzResearch.WordTrace]
  refine ⟨47345687779698209467977671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126255167412528558581273789 47345687779698209467977671)
  ·
    refine ⟨71018531669547314201966507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47345687779698209467977671 71018531669547314201966507)
    ·
      refine ⟨106527797504320971302949761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71018531669547314201966507 106527797504320971302949761)
      ·
        refine ⟨79895848128240728477212321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106527797504320971302949761 79895848128240728477212321)
        ·
          refine ⟨59921886096180546357909241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79895848128240728477212321 59921886096180546357909241)
          ·
            refine ⟨44941414572135409768431931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59921886096180546357909241 44941414572135409768431931)
            ·
              refine ⟨67412121858203114652647897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44941414572135409768431931 67412121858203114652647897)
              ·
                refine ⟨50559091393652335989485923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67412121858203114652647897 50559091393652335989485923)
                ·
                  refine ⟨75838637090478503984228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50559091393652335989485923 75838637090478503984228885)
                  ·
                    refine ⟨3554936113616179874260729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75838637090478503984228885 3554936113616179874260729)
                    ·
                      refine ⟨2666202085212134905695547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3554936113616179874260729 2666202085212134905695547)
                      ·
                        rfl

theorem cell23_5192410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_5192410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192410 prefixEnd_5192410 := by exact prefixLift 5192410
  have htrace : WordTrace (prefixWord ++ tailWord_5192410) baseStart_5192410 baseEnd_5192410 := by
    simpa [prefixWord, tailWord_5192410, baseEnd_5192410] using wordTrace_append hprefix tailTrace_5192410
  have hstable : (prefixWord ++ tailWord_5192410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192410).length < 2 ^ (prefixWord ++ tailWord_5192410).sum := by decide
  have hdescent : baseEnd_5192410 < baseStart_5192410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192433 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 8]
def baseStart_5192433 : Nat := 118140960795 + 5192433 * 2 ^ 59
def prefixEnd_5192433 : Nat := 4983230072969 + 3 ^ 40 * 5192433 * 2
def baseEnd_5192433 : Nat := 296245988363020923967549

theorem tailTrace_5192433 : CollatzResearch.WordTrace tailWord_5192433 prefixEnd_5192433 296245988363020923967549 := by
  unfold tailWord_5192433
  simp only [CollatzResearch.WordTrace]
  refine ⟨189383589997709512799997953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126255726665139675199998635 189383589997709512799997953)
  ·
    refine ⟨142037692498282134599998465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189383589997709512799997953 142037692498282134599998465)
    ·
      refine ⟨106528269373711600949998849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142037692498282134599998465 106528269373711600949998849)
      ·
        refine ⟨79896202030283700712499137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106528269373711600949998849 79896202030283700712499137)
        ·
          refine ⟨59922151522712775534374353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79896202030283700712499137 59922151522712775534374353)
          ·
            refine ⟨44941613642034581650780765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59922151522712775534374353 44941613642034581650780765)
            ·
              refine ⟨16853105115762968119042787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44941613642034581650780765 16853105115762968119042787)
              ·
                refine ⟨25279657673644452178564181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16853105115762968119042787 25279657673644452178564181)
                ·
                  refine ⟨296245988363020923967549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25279657673644452178564181 296245988363020923967549)
                  ·
                    rfl

theorem cell23_5192433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_5192433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192433 prefixEnd_5192433 := by exact prefixLift 5192433
  have htrace : WordTrace (prefixWord ++ tailWord_5192433) baseStart_5192433 baseEnd_5192433 := by
    simpa [prefixWord, tailWord_5192433, baseEnd_5192433] using wordTrace_append hprefix tailTrace_5192433
  have hstable : (prefixWord ++ tailWord_5192433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192433).length < 2 ^ (prefixWord ++ tailWord_5192433).sum := by decide
  have hdescent : baseEnd_5192433 < baseStart_5192433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192471 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 1, 4]
def baseStart_5192471 : Nat := 118140960795 + 5192471 * 2 ^ 59
def prefixEnd_5192471 : Nat := 4983230072969 + 3 ^ 40 * 5192471 * 2
def baseEnd_5192471 : Nat := 888744469177353055677589

theorem tailTrace_5192471 : CollatzResearch.WordTrace tailWord_5192471 prefixEnd_5192471 888744469177353055677589 := by
  unfold tailWord_5192471
  simp only [CollatzResearch.WordTrace]
  refine ⟨189384975971571845289881267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126256650647714563526587511 189384975971571845289881267)
  ·
    refine ⟨284077463957357767934821901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189384975971571845289881267 284077463957357767934821901)
    ·
      refine ⟨106529048984009162975558213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284077463957357767934821901 106529048984009162975558213)
      ·
        refine ⟨19974196684501718057917165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106529048984009162975558213 19974196684501718057917165)
        ·
          refine ⟨7490323756688144271718937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19974196684501718057917165 7490323756688144271718937)
          ·
            refine ⟨5617742817516108203789203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7490323756688144271718937 5617742817516108203789203)
            ·
              refine ⟨8426614226274162305683805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617742817516108203789203 8426614226274162305683805)
              ·
                refine ⟨3159980334852810864631427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8426614226274162305683805 3159980334852810864631427)
                ·
                  refine ⟨4739970502279216296947141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3159980334852810864631427 4739970502279216296947141)
                  ·
                    refine ⟨888744469177353055677589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4739970502279216296947141 888744469177353055677589)
                    ·
                      rfl

theorem cell23_5192471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_5192471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192471 prefixEnd_5192471 := by exact prefixLift 5192471
  have htrace : WordTrace (prefixWord ++ tailWord_5192471) baseStart_5192471 baseEnd_5192471 := by
    simpa [prefixWord, tailWord_5192471, baseEnd_5192471] using wordTrace_append hprefix tailTrace_5192471
  have hstable : (prefixWord ++ tailWord_5192471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192471).length < 2 ^ (prefixWord ++ tailWord_5192471).sum := by decide
  have hdescent : baseEnd_5192471 < baseStart_5192471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192537 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 5]
def baseStart_5192537 : Nat := 118140960795 + 5192537 * 2 ^ 59
def prefixEnd_5192537 : Nat := 4983230072969 + 3 ^ 40 * 5192537 * 2
def baseEnd_5192537 : Nat := 2666267297255255908807463

theorem tailTrace_5192537 : CollatzResearch.WordTrace tailWord_5192537 prefixEnd_5192537 2666267297255255908807463 := by
  unfold tailWord_5192537
  simp only [CollatzResearch.WordTrace]
  refine ⟨189387383189332738561783865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126258255459555159041189243 189387383189332738561783865)
  ·
    refine ⟨142040537391999553921337899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189387383189332738561783865 142040537391999553921337899)
    ·
      refine ⟨213060806087999330882006849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142040537391999553921337899 213060806087999330882006849)
      ·
        refine ⟨159795604565999498161505137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213060806087999330882006849 159795604565999498161505137)
        ·
          refine ⟨119846703424499623621128853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159795604565999498161505137 119846703424499623621128853)
          ·
            refine ⟨5617814223023419857240415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119846703424499623621128853 5617814223023419857240415)
            ·
              refine ⟨8426721334535129785860623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617814223023419857240415 8426721334535129785860623)
              ·
                refine ⟨12640082001802694678790935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8426721334535129785860623 12640082001802694678790935)
                ·
                  refine ⟨18960123002704042018186403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12640082001802694678790935 18960123002704042018186403)
                  ·
                    refine ⟨28440184504056063027279605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18960123002704042018186403 28440184504056063027279605)
                    ·
                      refine ⟨2666267297255255908807463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28440184504056063027279605 2666267297255255908807463)
                      ·
                        rfl

theorem cell23_5192537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_5192537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192537 prefixEnd_5192537 := by exact prefixLift 5192537
  have htrace : WordTrace (prefixWord ++ tailWord_5192537) baseStart_5192537 baseEnd_5192537 := by
    simpa [prefixWord, tailWord_5192537, baseEnd_5192537] using wordTrace_append hprefix tailTrace_5192537
  have hstable : (prefixWord ++ tailWord_5192537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192537).length < 2 ^ (prefixWord ++ tailWord_5192537).sum := by decide
  have hdescent : baseEnd_5192537 < baseStart_5192537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192540 : List Nat := [2, 2, 4, 2, 1, 12]
def baseStart_5192540 : Nat := 118140960795 + 5192540 * 2 ^ 59
def prefixEnd_5192540 : Nat := 4983230072969 + 3 ^ 40 * 5192540 * 2
def baseEnd_5192540 : Nat := 10972299743609956366543

theorem tailTrace_5192540 : CollatzResearch.WordTrace tailWord_5192540 prefixEnd_5192540 10972299743609956366543 := by
  unfold tailWord_5192540
  simp only [CollatzResearch.WordTrace]
  refine ⟨94693746304160935037071537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126258328405547913382762049 94693746304160935037071537)
  ·
    refine ⟨71020309728120701277803653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94693746304160935037071537 71020309728120701277803653)
    ·
      refine ⟨13316308074022631489588185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71020309728120701277803653 13316308074022631489588185)
      ·
        refine ⟨9987231055516973617191139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13316308074022631489588185 9987231055516973617191139)
        ·
          refine ⟨14980846583275460425786709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987231055516973617191139 14980846583275460425786709)
          ·
            refine ⟨10972299743609956366543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14980846583275460425786709 10972299743609956366543)
            ·
              rfl

theorem cell23_5192540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 12].length) (baseStart_5192540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192540 prefixEnd_5192540 := by exact prefixLift 5192540
  have htrace : WordTrace (prefixWord ++ tailWord_5192540) baseStart_5192540 baseEnd_5192540 := by
    simpa [prefixWord, tailWord_5192540, baseEnd_5192540] using wordTrace_append hprefix tailTrace_5192540
  have hstable : (prefixWord ++ tailWord_5192540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192540).length < 2 ^ (prefixWord ++ tailWord_5192540).sum := by decide
  have hdescent : baseEnd_5192540 < baseStart_5192540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192580 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_5192580 : Nat := 118140960795 + 5192580 * 2 ^ 59
def prefixEnd_5192580 : Nat := 4983230072969 + 3 ^ 40 * 5192580 * 2
def baseEnd_5192580 : Nat := 2666289376923399240569765

theorem tailTrace_5192580 : CollatzResearch.WordTrace tailWord_5192580 prefixEnd_5192580 2666289376923399240569765 := by
  unfold tailWord_5192580
  simp only [CollatzResearch.WordTrace]
  refine ⟨94694475764088478452799597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126259301018784637937066129 94694475764088478452799597)
  ·
    refine ⟨35510428411533179419799849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94694475764088478452799597 35510428411533179419799849)
    ·
      refine ⟨26632821308649884564849887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35510428411533179419799849 26632821308649884564849887)
      ·
        refine ⟨39949231962974826847274831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26632821308649884564849887 39949231962974826847274831)
        ·
          refine ⟨59923847944462240270912247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39949231962974826847274831 59923847944462240270912247)
          ·
            refine ⟨89885771916693360406368371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59923847944462240270912247 89885771916693360406368371)
            ·
              refine ⟨134828657875040040609552557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89885771916693360406368371 134828657875040040609552557)
              ·
                refine ⟨50560746703140015228582209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134828657875040040609552557 50560746703140015228582209)
                ·
                  refine ⟨37920560027355011421436657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50560746703140015228582209 37920560027355011421436657)
                  ·
                    refine ⟨28440420020516258566077493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37920560027355011421436657 28440420020516258566077493)
                    ·
                      refine ⟨2666289376923399240569765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28440420020516258566077493 2666289376923399240569765)
                      ·
                        rfl

theorem cell23_5192580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_5192580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192580 prefixEnd_5192580 := by exact prefixLift 5192580
  have htrace : WordTrace (prefixWord ++ tailWord_5192580) baseStart_5192580 baseEnd_5192580 := by
    simpa [prefixWord, tailWord_5192580, baseEnd_5192580] using wordTrace_append hprefix tailTrace_5192580
  have hstable : (prefixWord ++ tailWord_5192580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192580).length < 2 ^ (prefixWord ++ tailWord_5192580).sum := by decide
  have hdescent : baseEnd_5192580 < baseStart_5192580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192628 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5192628 : Nat := 118140960795 + 5192628 * 2 ^ 59
def prefixEnd_5192628 : Nat := 4983230072969 + 3 ^ 40 * 5192628 * 2
def baseEnd_5192628 : Nat := 2666314023994815052769545

theorem tailTrace_5192628 : CollatzResearch.WordTrace tailWord_5192628 prefixEnd_5192628 2666314023994815052769545 := by
  unfold tailWord_5192628
  simp only [CollatzResearch.WordTrace]
  refine ⟨94695351116001530551673269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126260468154668707402231025 94695351116001530551673269)
  ·
    refine ⟨8877689167125143489219369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94695351116001530551673269 8877689167125143489219369)
    ·
      refine ⟨6658266875343857616914527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8877689167125143489219369 6658266875343857616914527)
      ·
        refine ⟨9987400313015786425371791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6658266875343857616914527 9987400313015786425371791)
        ·
          refine ⟨14981100469523679638057687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987400313015786425371791 14981100469523679638057687)
          ·
            refine ⟨22471650704285519457086531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14981100469523679638057687 22471650704285519457086531)
            ·
              refine ⟨33707476056428279185629797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22471650704285519457086531 33707476056428279185629797)
              ·
                refine ⟨6320151760580302347305587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33707476056428279185629797 6320151760580302347305587)
                ·
                  refine ⟨9480227640870453520958381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6320151760580302347305587 9480227640870453520958381)
                  ·
                    refine ⟨3555085365326420070359393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9480227640870453520958381 3555085365326420070359393)
                    ·
                      refine ⟨2666314023994815052769545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555085365326420070359393 2666314023994815052769545)
                      ·
                        rfl

theorem cell23_5192628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5192628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192628 prefixEnd_5192628 := by exact prefixLift 5192628
  have htrace : WordTrace (prefixWord ++ tailWord_5192628) baseStart_5192628 baseEnd_5192628 := by
    simpa [prefixWord, tailWord_5192628, baseEnd_5192628] using wordTrace_append hprefix tailTrace_5192628
  have hstable : (prefixWord ++ tailWord_5192628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192628).length < 2 ^ (prefixWord ++ tailWord_5192628).sum := by decide
  have hdescent : baseEnd_5192628 < baseStart_5192628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192692 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5192692 : Nat := 118140960795 + 5192692 * 2 ^ 59
def prefixEnd_5192692 : Nat := 4983230072969 + 3 ^ 40 * 5192692 * 2
def baseEnd_5192692 : Nat := 2666346886756702802369251

theorem tailTrace_5192692 : CollatzResearch.WordTrace tailWord_5192692 prefixEnd_5192692 2666346886756702802369251 := by
  unfold tailWord_5192692
  simp only [CollatzResearch.WordTrace]
  refine ⟨94696518251885600016838165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126262024335847466689117553 94696518251885600016838165)
  ·
    refine ⟨4438899293057137500789289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94696518251885600016838165 4438899293057137500789289)
    ·
      refine ⟨3329174469792853125591967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4438899293057137500789289 3329174469792853125591967)
      ·
        refine ⟨4993761704689279688387951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329174469792853125591967 4993761704689279688387951)
        ·
          refine ⟨7490642557033919532581927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993761704689279688387951 7490642557033919532581927)
          ·
            refine ⟨11235963835550879298872891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7490642557033919532581927 11235963835550879298872891)
            ·
              refine ⟨16853945753326318948309337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11235963835550879298872891 16853945753326318948309337)
              ·
                refine ⟨12640459314994739211232003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16853945753326318948309337 12640459314994739211232003)
                ·
                  refine ⟨18960688972492108816848005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12640459314994739211232003 18960688972492108816848005)
                  ·
                    refine ⟨3555129182342270403159001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18960688972492108816848005 3555129182342270403159001)
                    ·
                      refine ⟨2666346886756702802369251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555129182342270403159001 2666346886756702802369251)
                      ·
                        rfl

theorem cell23_5192692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5192692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192692 prefixEnd_5192692 := by exact prefixLift 5192692
  have htrace : WordTrace (prefixWord ++ tailWord_5192692) baseStart_5192692 baseEnd_5192692 := by
    simpa [prefixWord, tailWord_5192692, baseEnd_5192692] using wordTrace_append hprefix tailTrace_5192692
  have hstable : (prefixWord ++ tailWord_5192692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192692).length < 2 ^ (prefixWord ++ tailWord_5192692).sum := by decide
  have hdescent : baseEnd_5192692 < baseStart_5192692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192694 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_5192694 : Nat := 118140960795 + 5192694 * 2 ^ 59
def prefixEnd_5192694 : Nat := 4983230072969 + 3 ^ 40 * 5192694 * 2
def baseEnd_5192694 : Nat := 888782637906003931514747

theorem tailTrace_5192694 : CollatzResearch.WordTrace tailWord_5192694 prefixEnd_5192694 888782637906003931514747 := by
  unfold tailWord_5192694
  simp only [CollatzResearch.WordTrace]
  refine ⟨11837069340610247148453071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126262072966509302916832757 11837069340610247148453071)
  ·
    refine ⟨17755604010915370722679607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11837069340610247148453071 17755604010915370722679607)
    ·
      refine ⟨26633406016373056084019411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17755604010915370722679607 26633406016373056084019411)
      ·
        refine ⟨39950109024559584126029117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26633406016373056084019411 39950109024559584126029117)
        ·
          refine ⟨14981290884209844047260919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39950109024559584126029117 14981290884209844047260919)
          ·
            refine ⟨22471936326314766070891379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14981290884209844047260919 22471936326314766070891379)
            ·
              refine ⟨33707904489472149106337069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22471936326314766070891379 33707904489472149106337069)
              ·
                refine ⟨12640464183552055914876401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33707904489472149106337069 12640464183552055914876401)
                ·
                  refine ⟨9480348137664041936157301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12640464183552055914876401 9480348137664041936157301)
                  ·
                    refine ⟨888782637906003931514747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9480348137664041936157301 888782637906003931514747)
                    ·
                      rfl

theorem cell23_5192694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_5192694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192694 prefixEnd_5192694 := by exact prefixLift 5192694
  have htrace : WordTrace (prefixWord ++ tailWord_5192694) baseStart_5192694 baseEnd_5192694 := by
    simpa [prefixWord, tailWord_5192694, baseEnd_5192694] using wordTrace_append hprefix tailTrace_5192694
  have hstable : (prefixWord ++ tailWord_5192694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192694).length < 2 ^ (prefixWord ++ tailWord_5192694).sum := by decide
  have hdescent : baseEnd_5192694 < baseStart_5192694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192714 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5192714 : Nat := 118140960795 + 5192714 * 2 ^ 59
def prefixEnd_5192714 : Nat := 4983230072969 + 3 ^ 40 * 5192714 * 2
def baseEnd_5192714 : Nat := 2666358183331101716294149

theorem tailTrace_5192714 : CollatzResearch.WordTrace tailWord_5192714 prefixEnd_5192714 2666358183331101716294149 := by
  unfold tailWord_5192714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47348459727422874447744299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126262559273127665193984797 47348459727422874447744299)
  ·
    refine ⟨71022689591134311671616449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47348459727422874447744299 71022689591134311671616449)
    ·
      refine ⟨53267017193350733753712337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71022689591134311671616449 53267017193350733753712337)
      ·
        refine ⟨39950262895013050315284253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53267017193350733753712337 39950262895013050315284253)
        ·
          refine ⟨14981348585629893868231595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39950262895013050315284253 14981348585629893868231595)
          ·
            refine ⟨22472022878444840802347393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14981348585629893868231595 22472022878444840802347393)
            ·
              refine ⟨16854017158833630601760545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22472022878444840802347393 16854017158833630601760545)
              ·
                refine ⟨12640512869125222951320409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16854017158833630601760545 12640512869125222951320409)
                ·
                  refine ⟨9480384651843917213490307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12640512869125222951320409 9480384651843917213490307)
                  ·
                    refine ⟨14220576977765875820235461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9480384651843917213490307 14220576977765875820235461)
                    ·
                      refine ⟨2666358183331101716294149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14220576977765875820235461 2666358183331101716294149)
                      ·
                        rfl

theorem cell23_5192714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5192714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192714 prefixEnd_5192714 := by exact prefixLift 5192714
  have htrace : WordTrace (prefixWord ++ tailWord_5192714) baseStart_5192714 baseEnd_5192714 := by
    simpa [prefixWord, tailWord_5192714, baseEnd_5192714] using wordTrace_append hprefix tailTrace_5192714
  have hstable : (prefixWord ++ tailWord_5192714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192714).length < 2 ^ (prefixWord ++ tailWord_5192714).sum := by decide
  have hdescent : baseEnd_5192714 < baseStart_5192714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192758 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5192758 : Nat := 118140960795 + 5192758 * 2 ^ 59
def prefixEnd_5192758 : Nat := 4983230072969 + 3 ^ 40 * 5192758 * 2
def baseEnd_5192758 : Nat := 888793592159966514714649

theorem tailTrace_5192758 : CollatzResearch.WordTrace tailWord_5192758 prefixEnd_5192758 888793592159966514714649 := by
  unfold tailWord_5192758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11837215232595755831598683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126263629147688062203719285 11837215232595755831598683)
  ·
    refine ⟨17755822848893633747398025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11837215232595755831598683 17755822848893633747398025)
    ·
      refine ⟨13316867136670225310548519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17755822848893633747398025 13316867136670225310548519)
      ·
        refine ⟨19975300705005337965822779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13316867136670225310548519 19975300705005337965822779)
        ·
          refine ⟨29962951057508006948734169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19975300705005337965822779 29962951057508006948734169)
          ·
            refine ⟨22472213293131005211550627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29962951057508006948734169 22472213293131005211550627)
            ·
              refine ⟨33708319939696507817325941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22472213293131005211550627 33708319939696507817325941)
              ·
                refine ⟨3160154994346547607874307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33708319939696507817325941 3160154994346547607874307)
                ·
                  refine ⟨4740232491519821411811461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160154994346547607874307 4740232491519821411811461)
                  ·
                    refine ⟨888793592159966514714649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4740232491519821411811461 888793592159966514714649)
                    ·
                      rfl

theorem cell23_5192758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5192758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192758 prefixEnd_5192758 := by exact prefixLift 5192758
  have htrace : WordTrace (prefixWord ++ tailWord_5192758) baseStart_5192758 baseEnd_5192758 := by
    simpa [prefixWord, tailWord_5192758, baseEnd_5192758] using wordTrace_append hprefix tailTrace_5192758
  have hstable : (prefixWord ++ tailWord_5192758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192758).length < 2 ^ (prefixWord ++ tailWord_5192758).sum := by decide
  have hdescent : baseEnd_5192758 < baseStart_5192758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192804 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_5192804 : Nat := 118140960795 + 5192804 * 2 ^ 59
def prefixEnd_5192804 : Nat := 4983230072969 + 3 ^ 40 * 5192804 * 2
def baseEnd_5192804 : Nat := 2666404396590006364168735

theorem tailTrace_5192804 : CollatzResearch.WordTrace tailWord_5192804 prefixEnd_5192804 2666404396590006364168735 := by
  unfold tailWord_5192804
  simp only [CollatzResearch.WordTrace]
  refine ⟨94698560739682721580876733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126264747652910295441168977 94698560739682721580876733)
  ·
    refine ⟨35511960277381020592828775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94698560739682721580876733 35511960277381020592828775)
    ·
      refine ⟨53267940416071530889243163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35511960277381020592828775 53267940416071530889243163)
      ·
        refine ⟨79901910624107296333864745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53267940416071530889243163 79901910624107296333864745)
        ·
          refine ⟨59926432968080472250398559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79901910624107296333864745 59926432968080472250398559)
          ·
            refine ⟨89889649452120708375597839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59926432968080472250398559 89889649452120708375597839)
            ·
              refine ⟨134834474178181062563396759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89889649452120708375597839 134834474178181062563396759)
              ·
                refine ⟨202251711267271593845095139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134834474178181062563396759 202251711267271593845095139)
                ·
                  refine ⟨303377566900907390767642709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202251711267271593845095139 303377566900907390767642709)
                  ·
                    refine ⟨3555205862120008485558313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 303377566900907390767642709 3555205862120008485558313)
                    ·
                      refine ⟨2666404396590006364168735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555205862120008485558313 2666404396590006364168735)
                      ·
                        rfl

theorem cell23_5192804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_5192804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192804 prefixEnd_5192804 := by exact prefixLift 5192804
  have htrace : WordTrace (prefixWord ++ tailWord_5192804) baseStart_5192804 baseEnd_5192804 := by
    simpa [prefixWord, tailWord_5192804, baseEnd_5192804] using wordTrace_append hprefix tailTrace_5192804
  have hstable : (prefixWord ++ tailWord_5192804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192804).length < 2 ^ (prefixWord ++ tailWord_5192804).sum := by decide
  have hdescent : baseEnd_5192804 < baseStart_5192804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192858 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5192858 : Nat := 118140960795 + 5192858 * 2 ^ 59
def prefixEnd_5192858 : Nat := 4983230072969 + 3 ^ 40 * 5192858 * 2
def baseEnd_5192858 : Nat := 2666432124545349152893487

theorem tailTrace_5192858 : CollatzResearch.WordTrace tailWord_5192858 prefixEnd_5192858 2666432124545349152893487 := by
  unfold tailWord_5192858
  simp only [CollatzResearch.WordTrace]
  refine ⟨47349772755292452596054807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126266060680779873589479485 47349772755292452596054807)
  ·
    refine ⟨71024659132938678894082211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47349772755292452596054807 71024659132938678894082211)
    ·
      refine ⟨106536988699408018341123317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71024659132938678894082211 106536988699408018341123317)
      ·
        refine ⟨9987842690569501719480311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106536988699408018341123317 9987842690569501719480311)
        ·
          refine ⟨14981764035854252579220467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987842690569501719480311 14981764035854252579220467)
          ·
            refine ⟨22472646053781378868830701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14981764035854252579220467 22472646053781378868830701)
            ·
              refine ⟨8427242270168017075811513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22472646053781378868830701 8427242270168017075811513)
              ·
                refine ⟨6320431702626012806858635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8427242270168017075811513 6320431702626012806858635)
                ·
                  refine ⟨9480647553939019210287953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6320431702626012806858635 9480647553939019210287953)
                  ·
                    refine ⟨7110485665454264407715965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9480647553939019210287953 7110485665454264407715965)
                    ·
                      refine ⟨2666432124545349152893487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7110485665454264407715965 2666432124545349152893487)
                      ·
                        rfl

theorem cell23_5192858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5192858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192858 prefixEnd_5192858 := by exact prefixLift 5192858
  have htrace : WordTrace (prefixWord ++ tailWord_5192858) baseStart_5192858 baseEnd_5192858 := by
    simpa [prefixWord, tailWord_5192858, baseEnd_5192858] using wordTrace_append hprefix tailTrace_5192858
  have hstable : (prefixWord ++ tailWord_5192858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192858).length < 2 ^ (prefixWord ++ tailWord_5192858).sum := by decide
  have hdescent : baseEnd_5192858 < baseStart_5192858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192867 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5192867 : Nat := 118140960795 + 5192867 * 2 ^ 59
def prefixEnd_5192867 : Nat := 4983230072969 + 3 ^ 40 * 5192867 * 2
def baseEnd_5192867 : Nat := 2666436745871239617680945

theorem tailTrace_5192867 : CollatzResearch.WordTrace tailWord_5192867 prefixEnd_5192867 2666436745871239617680945 := by
  unfold tailWord_5192867
  simp only [CollatzResearch.WordTrace]
  refine ⟨189399419278137204921296855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126266279518758136614197903 189399419278137204921296855)
  ·
    refine ⟨284099128917205807381945283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189399419278137204921296855 284099128917205807381945283)
    ·
      refine ⟨426148693375808711072917925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284099128917205807381945283 426148693375808711072917925)
      ·
        refine ⟨79902880007964133326172111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 426148693375808711072917925 79902880007964133326172111)
        ·
          refine ⟨119854320011946199989258167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79902880007964133326172111 119854320011946199989258167)
          ·
            refine ⟨179781480017919299983887251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119854320011946199989258167 179781480017919299983887251)
            ·
              refine ⟨269672220026878949975830877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179781480017919299983887251 269672220026878949975830877)
              ·
                refine ⟨101127082510079606240936579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269672220026878949975830877 101127082510079606240936579)
                ·
                  refine ⟨151690623765119409361404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101127082510079606240936579 151690623765119409361404869)
                  ·
                    refine ⟨28441991955959889255263413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151690623765119409361404869 28441991955959889255263413)
                    ·
                      refine ⟨2666436745871239617680945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28441991955959889255263413 2666436745871239617680945)
                      ·
                        rfl

theorem cell23_5192867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5192867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192867 prefixEnd_5192867 := by exact prefixLift 5192867
  have htrace : WordTrace (prefixWord ++ tailWord_5192867) baseStart_5192867 baseEnd_5192867 := by
    simpa [prefixWord, tailWord_5192867, baseEnd_5192867] using wordTrace_append hprefix tailTrace_5192867
  have hstable : (prefixWord ++ tailWord_5192867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192867).length < 2 ^ (prefixWord ++ tailWord_5192867).sum := by decide
  have hdescent : baseEnd_5192867 < baseStart_5192867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192871 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_5192871 : Nat := 118140960795 + 5192871 * 2 ^ 59
def prefixEnd_5192871 : Nat := 4983230072969 + 3 ^ 40 * 5192871 * 2
def baseEnd_5192871 : Nat := 2666438799793857602030927

theorem tailTrace_5192871 : CollatzResearch.WordTrace tailWord_5192871 prefixEnd_5192871 2666438799793857602030927 := by
  unfold tailWord_5192871
  simp only [CollatzResearch.WordTrace]
  refine ⟨189399565170122713604442467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126266376780081809069628311 189399565170122713604442467)
  ·
    refine ⟨284099347755184070406663701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189399565170122713604442467 284099347755184070406663701)
    ·
      refine ⟨13317156926024253300312361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 284099347755184070406663701 13317156926024253300312361)
      ·
        refine ⟨9987867694518189975234271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13317156926024253300312361 9987867694518189975234271)
        ·
          refine ⟨14981801541777284962851407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987867694518189975234271 14981801541777284962851407)
          ·
            refine ⟨22472702312665927444277111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14981801541777284962851407 22472702312665927444277111)
            ·
              refine ⟨33709053468998891166415667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22472702312665927444277111 33709053468998891166415667)
              ·
                refine ⟨50563580203498336749623501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33709053468998891166415667 50563580203498336749623501)
                ·
                  refine ⟨18961342576311876281108813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50563580203498336749623501 18961342576311876281108813)
                  ·
                    refine ⟨7110503466116953605415805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18961342576311876281108813 7110503466116953605415805)
                    ·
                      refine ⟨2666438799793857602030927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7110503466116953605415805 2666438799793857602030927)
                      ·
                        rfl

theorem cell23_5192871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_5192871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192871 prefixEnd_5192871 := by exact prefixLift 5192871
  have htrace : WordTrace (prefixWord ++ tailWord_5192871) baseStart_5192871 baseEnd_5192871 := by
    simpa [prefixWord, tailWord_5192871, baseEnd_5192871] using wordTrace_append hprefix tailTrace_5192871
  have hstable : (prefixWord ++ tailWord_5192871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192871).length < 2 ^ (prefixWord ++ tailWord_5192871).sum := by decide
  have hdescent : baseEnd_5192871 < baseStart_5192871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192902 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5192902 : Nat := 118140960795 + 5192902 * 2 ^ 59
def prefixEnd_5192902 : Nat := 4983230072969 + 3 ^ 40 * 5192902 * 2
def baseEnd_5192902 : Nat := 2666454717694146980743285

theorem tailTrace_5192902 : CollatzResearch.WordTrace tailWord_5192902 prefixEnd_5192902 2666454717694146980743285 := by
  unfold tailWord_5192902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918771744781575184338155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126267130555340270599213973 5918771744781575184338155)
  ·
    refine ⟨8878157617172362776507233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5918771744781575184338155 8878157617172362776507233)
    ·
      refine ⟨6658618212879272082380425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8878157617172362776507233 6658618212879272082380425)
      ·
        refine ⟨4993963659659454061785319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6658618212879272082380425 4993963659659454061785319)
        ·
          refine ⟨7490945489489181092677979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993963659659454061785319 7490945489489181092677979)
          ·
            refine ⟨11236418234233771639016969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7490945489489181092677979 11236418234233771639016969)
            ·
              refine ⟨8427313675675328729262727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11236418234233771639016969 8427313675675328729262727)
              ·
                refine ⟨12640970513512993093894091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8427313675675328729262727 12640970513512993093894091)
                ·
                  refine ⟨18961455770269489640841137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12640970513512993093894091 18961455770269489640841137)
                  ·
                    refine ⟨14221091827702117230630853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18961455770269489640841137 14221091827702117230630853)
                    ·
                      refine ⟨2666454717694146980743285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14221091827702117230630853 2666454717694146980743285)
                      ·
                        rfl

theorem cell23_5192902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5192902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192902 prefixEnd_5192902 := by exact prefixLift 5192902
  have htrace : WordTrace (prefixWord ++ tailWord_5192902) baseStart_5192902 baseEnd_5192902 := by
    simpa [prefixWord, tailWord_5192902, baseEnd_5192902] using wordTrace_append hprefix tailTrace_5192902
  have hstable : (prefixWord ++ tailWord_5192902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192902).length < 2 ^ (prefixWord ++ tailWord_5192902).sum := by decide
  have hdescent : baseEnd_5192902 < baseStart_5192902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192941 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5192941 : Nat := 118140960795 + 5192941 * 2 ^ 59
def prefixEnd_5192941 : Nat := 4983230072969 + 3 ^ 40 * 5192941 * 2
def baseEnd_5192941 : Nat := 2666474743439672328155605

theorem tailTrace_5192941 : CollatzResearch.WordTrace tailWord_5192941 prefixEnd_5192941 2666474743439672328155605 := by
  unfold tailWord_5192941
  simp only [CollatzResearch.WordTrace]
  refine ⟨189402118279869115559490677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126268078853246077039660451 189402118279869115559490677)
  ·
    refine ⟨17756448588737729583702251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189402118279869115559490677 17756448588737729583702251)
    ·
      refine ⟨26634672883106594375553377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17756448588737729583702251 26634672883106594375553377)
      ·
        refine ⟨19976004662329945781665033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26634672883106594375553377 19976004662329945781665033)
        ·
          refine ⟨14982003496747459336248775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19976004662329945781665033 14982003496747459336248775)
          ·
            refine ⟨22473005245121189004373163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14982003496747459336248775 22473005245121189004373163)
            ·
              refine ⟨33709507867681783506559745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22473005245121189004373163 33709507867681783506559745)
              ·
                refine ⟨25282130900761337629919809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33709507867681783506559745 25282130900761337629919809)
                ·
                  refine ⟨18961598175571003222439857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25282130900761337629919809 18961598175571003222439857)
                  ·
                    refine ⟨14221198631678252416829893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18961598175571003222439857 14221198631678252416829893)
                    ·
                      refine ⟨2666474743439672328155605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14221198631678252416829893 2666474743439672328155605)
                      ·
                        rfl

theorem cell23_5192941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5192941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192941 prefixEnd_5192941 := by exact prefixLift 5192941
  have htrace : WordTrace (prefixWord ++ tailWord_5192941) baseStart_5192941 baseEnd_5192941 := by
    simpa [prefixWord, tailWord_5192941, baseEnd_5192941] using wordTrace_append hprefix tailTrace_5192941
  have hstable : (prefixWord ++ tailWord_5192941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192941).length < 2 ^ (prefixWord ++ tailWord_5192941).sum := by decide
  have hdescent : baseEnd_5192941 < baseStart_5192941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192961 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_5192961 : Nat := 118140960795 + 5192961 * 2 ^ 59
def prefixEnd_5192961 : Nat := 4983230072969 + 3 ^ 40 * 5192961 * 2
def baseEnd_5192961 : Nat := 2666485013052762249905513

theorem tailTrace_5192961 : CollatzResearch.WordTrace tailWord_5192961 prefixEnd_5192961 2666485013052762249905513 := by
  unfold tailWord_5192961
  simp only [CollatzResearch.WordTrace]
  refine ⟨189402847739796658975218737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126268565159864439316812491 189402847739796658975218737)
  ·
    refine ⟨142052135804847494231414053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189402847739796658975218737 142052135804847494231414053)
    ·
      refine ⟨26634775463408905168390135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142052135804847494231414053 26634775463408905168390135)
      ·
        refine ⟨39952163195113357752585203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26634775463408905168390135 39952163195113357752585203)
        ·
          refine ⟨59928244792670036628877805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39952163195113357752585203 59928244792670036628877805)
          ·
            refine ⟨22473091797251263735829177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59928244792670036628877805 22473091797251263735829177)
            ·
              refine ⟨16854818847938447801871883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22473091797251263735829177 16854818847938447801871883)
              ·
                refine ⟨25282228271907671702807825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16854818847938447801871883 25282228271907671702807825)
                ·
                  refine ⟨18961671203930753777105869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25282228271907671702807825 18961671203930753777105869)
                  ·
                    refine ⟨7110626701474032666414701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18961671203930753777105869 7110626701474032666414701)
                    ·
                      refine ⟨2666485013052762249905513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7110626701474032666414701 2666485013052762249905513)
                      ·
                        rfl

theorem cell23_5192961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_5192961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192961 prefixEnd_5192961 := by exact prefixLift 5192961
  have htrace : WordTrace (prefixWord ++ tailWord_5192961) baseStart_5192961 baseEnd_5192961 := by
    simpa [prefixWord, tailWord_5192961, baseEnd_5192961] using wordTrace_append hprefix tailTrace_5192961
  have hstable : (prefixWord ++ tailWord_5192961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192961).length < 2 ^ (prefixWord ++ tailWord_5192961).sum := by decide
  have hdescent : baseEnd_5192961 < baseStart_5192961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5192962 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5192962 : Nat := 118140960795 + 5192962 * 2 ^ 59
def prefixEnd_5192962 : Nat := 4983230072969 + 3 ^ 40 * 5192962 * 2
def baseEnd_5192962 : Nat := 2666485526533416745993009

theorem tailTrace_5192962 : CollatzResearch.WordTrace tailWord_5192962 prefixEnd_5192962 2666485526533416745993009 := by
  unfold tailWord_5192962
  simp only [CollatzResearch.WordTrace]
  refine ⟨47350721053198259036501285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126268589475195357430670093 47350721053198259036501285)
  ·
    refine ⟨8878260197474673569343991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47350721053198259036501285 8878260197474673569343991)
    ·
      refine ⟨13317390296212010354015987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8878260197474673569343991 13317390296212010354015987)
      ·
        refine ⟨19976085444318015531023981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13317390296212010354015987 19976085444318015531023981)
        ·
          refine ⟨7491032041619255824133993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19976085444318015531023981 7491032041619255824133993)
          ·
            refine ⟨5618274031214441868100495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7491032041619255824133993 5618274031214441868100495)
            ·
              refine ⟨8427411046821662802150743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5618274031214441868100495 8427411046821662802150743)
              ·
                refine ⟨12641116570232494203226115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8427411046821662802150743 12641116570232494203226115)
                ·
                  refine ⟨18961674855348741304839173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12641116570232494203226115 18961674855348741304839173)
                  ·
                    refine ⟨3555314035377888994657345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18961674855348741304839173 3555314035377888994657345)
                    ·
                      refine ⟨2666485526533416745993009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555314035377888994657345 2666485526533416745993009)
                      ·
                        rfl

theorem cell23_5192962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5192962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5192962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5192962 prefixEnd_5192962 := by exact prefixLift 5192962
  have htrace : WordTrace (prefixWord ++ tailWord_5192962) baseStart_5192962 baseEnd_5192962 := by
    simpa [prefixWord, tailWord_5192962, baseEnd_5192962] using wordTrace_append hprefix tailTrace_5192962
  have hstable : (prefixWord ++ tailWord_5192962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5192962).length < 2 ^ (prefixWord ++ tailWord_5192962).sum := by decide
  have hdescent : baseEnd_5192962 < baseStart_5192962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5192962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193038 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_5193038 : Nat := 118140960795 + 5193038 * 2 ^ 59
def prefixEnd_5193038 : Nat := 4983230072969 + 3 ^ 40 * 5193038 * 2
def baseEnd_5193038 : Nat := 2666524551063158448642659

theorem tailTrace_5193038 : CollatzResearch.WordTrace tailWord_5193038 prefixEnd_5193038 2666524551063158448642659 := by
  unfold tailWord_5193038
  simp only [CollatzResearch.WordTrace]
  refine ⟨23675707020064712640721471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126270437440345134083847845 23675707020064712640721471)
  ·
    refine ⟨35513560530097068961082207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23675707020064712640721471 35513560530097068961082207)
    ·
      refine ⟨53270340795145603441623311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35513560530097068961082207 53270340795145603441623311)
      ·
        refine ⟨79905511192718405162434967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53270340795145603441623311 79905511192718405162434967)
        ·
          refine ⟨119858266789077607743652451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79905511192718405162434967 119858266789077607743652451)
          ·
            refine ⟨179787400183616411615478677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119858266789077607743652451 179787400183616411615478677)
            ·
              refine ⟨8427534383607019294475563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179787400183616411615478677 8427534383607019294475563)
              ·
                refine ⟨12641301575410528941713345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8427534383607019294475563 12641301575410528941713345)
                ·
                  refine ⟨9480976181557896706285009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12641301575410528941713345 9480976181557896706285009)
                  ·
                    refine ⟨7110732136168422529713757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9480976181557896706285009 7110732136168422529713757)
                    ·
                      refine ⟨2666524551063158448642659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7110732136168422529713757 2666524551063158448642659)
                      ·
                        rfl

theorem cell23_5193038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_5193038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193038 prefixEnd_5193038 := by exact prefixLift 5193038
  have htrace : WordTrace (prefixWord ++ tailWord_5193038) baseStart_5193038 baseEnd_5193038 := by
    simpa [prefixWord, tailWord_5193038, baseEnd_5193038] using wordTrace_append hprefix tailTrace_5193038
  have hstable : (prefixWord ++ tailWord_5193038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193038).length < 2 ^ (prefixWord ++ tailWord_5193038).sum := by decide
  have hdescent : baseEnd_5193038 < baseStart_5193038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193058 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_5193058 : Nat := 118140960795 + 5193058 * 2 ^ 59
def prefixEnd_5193058 : Nat := 4983230072969 + 3 ^ 40 * 5193058 * 2
def baseEnd_5193058 : Nat := 296281646741805374488063

theorem tailTrace_5193058 : CollatzResearch.WordTrace tailWord_5193058 prefixEnd_5193058 296281646741805374488063 := by
  unfold tailWord_5193058
  simp only [CollatzResearch.WordTrace]
  refine ⟨47351596405111311135374957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126270923746963496360999885 47351596405111311135374957)
  ·
    refine ⟨17756848651916741675765609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47351596405111311135374957 17756848651916741675765609)
    ·
      refine ⟨13317636488937556256824207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17756848651916741675765609 13317636488937556256824207)
      ·
        refine ⟨19976454733406334385236311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13317636488937556256824207 19976454733406334385236311)
        ·
          refine ⟨29964682100109501577854467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19976454733406334385236311 29964682100109501577854467)
          ·
            refine ⟨44947023150164252366781701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29964682100109501577854467 44947023150164252366781701)
            ·
              refine ⟨8427566840655797318771569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44947023150164252366781701 8427566840655797318771569)
              ·
                refine ⟨6320675130491847989078677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8427566840655797318771569 6320675130491847989078677)
                ·
                  refine ⟨296281646741805374488063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6320675130491847989078677 296281646741805374488063)
                  ·
                    rfl

theorem cell23_5193058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_5193058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193058 prefixEnd_5193058 := by exact prefixLift 5193058
  have htrace : WordTrace (prefixWord ++ tailWord_5193058) baseStart_5193058 baseEnd_5193058 := by
    simpa [prefixWord, tailWord_5193058, baseEnd_5193058] using wordTrace_append hprefix tailTrace_5193058
  have hstable : (prefixWord ++ tailWord_5193058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193058).length < 2 ^ (prefixWord ++ tailWord_5193058).sum := by decide
  have hdescent : baseEnd_5193058 < baseStart_5193058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193095 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_5193095 : Nat := 118140960795 + 5193095 * 2 ^ 59
def prefixEnd_5193095 : Nat := 4983230072969 + 3 ^ 40 * 5193095 * 2
def baseEnd_5193095 : Nat := 2666553819460464725629897

theorem tailTrace_5193095 : CollatzResearch.WordTrace tailWord_5193095 prefixEnd_5193095 2666553819460464725629897 := by
  unfold tailWord_5193095
  simp only [CollatzResearch.WordTrace]
  refine ⟨189407735121311199860596739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126271823414207466573731159 189407735121311199860596739)
  ·
    refine ⟨284111602681966799790895109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189407735121311199860596739 284111602681966799790895109)
    ·
      refine ⟨53270925502868774960792833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284111602681966799790895109 53270925502868774960792833)
      ·
        refine ⟨39953194127151581220594625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53270925502868774960792833 39953194127151581220594625)
        ·
          refine ⟨29964895595363685915445969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39953194127151581220594625 29964895595363685915445969)
          ·
            refine ⟨22473671696522764436584477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29964895595363685915445969 22473671696522764436584477)
            ·
              refine ⟨8427626886196036663719179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22473671696522764436584477 8427626886196036663719179)
              ·
                refine ⟨12641440329294054995578769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8427626886196036663719179 12641440329294054995578769)
                ·
                  refine ⟨9481080246970541246684077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12641440329294054995578769 9481080246970541246684077)
                  ·
                    refine ⟨3555405092613952967506529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9481080246970541246684077 3555405092613952967506529)
                    ·
                      refine ⟨2666553819460464725629897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555405092613952967506529 2666553819460464725629897)
                      ·
                        rfl

theorem cell23_5193095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_5193095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193095 prefixEnd_5193095 := by exact prefixLift 5193095
  have htrace : WordTrace (prefixWord ++ tailWord_5193095) baseStart_5193095 baseEnd_5193095 := by
    simpa [prefixWord, tailWord_5193095, baseEnd_5193095] using wordTrace_append hprefix tailTrace_5193095
  have hstable : (prefixWord ++ tailWord_5193095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193095).length < 2 ^ (prefixWord ++ tailWord_5193095).sum := by decide
  have hdescent : baseEnd_5193095 < baseStart_5193095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193111 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_5193111 : Nat := 118140960795 + 5193111 * 2 ^ 59
def prefixEnd_5193111 : Nat := 4983230072969 + 3 ^ 40 * 5193111 * 2
def baseEnd_5193111 : Nat := 2666562035150936663029823

theorem tailTrace_5193111 : CollatzResearch.WordTrace tailWord_5193111 prefixEnd_5193111 2666562035150936663029823 := by
  unfold tailWord_5193111
  simp only [CollatzResearch.WordTrace]
  refine ⟨189408318689253234593179187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126272212459502156395452791 189408318689253234593179187)
  ·
    refine ⟨284112478033879851889768781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189408318689253234593179187 284112478033879851889768781)
    ·
      refine ⟨106542179262704944458663293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284112478033879851889768781 106542179262704944458663293)
      ·
        refine ⟨39953317223514354171998735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106542179262704944458663293 39953317223514354171998735)
        ·
          refine ⟨59929975835271531257998103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39953317223514354171998735 59929975835271531257998103)
          ·
            refine ⟨89894963752907296886997155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59929975835271531257998103 89894963752907296886997155)
            ·
              refine ⟨134842445629360945330495733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89894963752907296886997155 134842445629360945330495733)
              ·
                refine ⟨12641479277752588624733975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134842445629360945330495733 12641479277752588624733975)
                ·
                  refine ⟨18962218916628882937100963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12641479277752588624733975 18962218916628882937100963)
                  ·
                    refine ⟨28443328374943324405651445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18962218916628882937100963 28443328374943324405651445)
                    ·
                      refine ⟨2666562035150936663029823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28443328374943324405651445 2666562035150936663029823)
                      ·
                        rfl

theorem cell23_5193111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_5193111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193111 prefixEnd_5193111 := by exact prefixLift 5193111
  have htrace : WordTrace (prefixWord ++ tailWord_5193111) baseStart_5193111 baseEnd_5193111 := by
    simpa [prefixWord, tailWord_5193111, baseEnd_5193111] using wordTrace_append hprefix tailTrace_5193111
  have hstable : (prefixWord ++ tailWord_5193111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193111).length < 2 ^ (prefixWord ++ tailWord_5193111).sum := by decide
  have hdescent : baseEnd_5193111 < baseStart_5193111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193148 : List Nat := [2, 2, 2, 4, 2, 1, 1, 9]
def baseStart_5193148 : Nat := 118140960795 + 5193148 * 2 ^ 59
def prefixEnd_5193148 : Nat := 4983230072969 + 3 ^ 40 * 5193148 * 2
def baseEnd_5193148 : Nat := 98762260516116778454339

theorem tailTrace_5193148 : CollatzResearch.WordTrace tailWord_5193148 prefixEnd_5193148 98762260516116778454339 := by
  unfold tailWord_5193148
  simp only [CollatzResearch.WordTrace]
  refine ⟨94704834095059594956138049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126273112126746126608184065 94704834095059594956138049)
  ·
    refine ⟨71028625571294696217103537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94704834095059594956138049 71028625571294696217103537)
    ·
      refine ⟨53271469178471022162827653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71028625571294696217103537 53271469178471022162827653)
      ·
        refine ⟨9988400470963316655530185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53271469178471022162827653 9988400470963316655530185)
        ·
          refine ⟨7491300353222487491647639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9988400470963316655530185 7491300353222487491647639)
          ·
            refine ⟨11236950529833731237471459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7491300353222487491647639 11236950529833731237471459)
            ·
              refine ⟨16855425794750596856207189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11236950529833731237471459 16855425794750596856207189)
              ·
                refine ⟨98762260516116778454339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16855425794750596856207189 98762260516116778454339)
                ·
                  rfl

theorem cell23_5193148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 9].length) (baseStart_5193148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193148 prefixEnd_5193148 := by exact prefixLift 5193148
  have htrace : WordTrace (prefixWord ++ tailWord_5193148) baseStart_5193148 baseEnd_5193148 := by
    simpa [prefixWord, tailWord_5193148, baseEnd_5193148] using wordTrace_append hprefix tailTrace_5193148
  have hstable : (prefixWord ++ tailWord_5193148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193148).length < 2 ^ (prefixWord ++ tailWord_5193148).sum := by decide
  have hdescent : baseEnd_5193148 < baseStart_5193148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193202 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5193202 : Nat := 118140960795 + 5193202 * 2 ^ 59
def prefixEnd_5193202 : Nat := 4983230072969 + 3 ^ 40 * 5193202 * 2
def baseEnd_5193202 : Nat := 2666608761890495806991905

theorem tailTrace_5193202 : CollatzResearch.WordTrace tailWord_5193202 prefixEnd_5193202 2666608761890495806991905 := by
  unfold tailWord_5193202
  simp only [CollatzResearch.WordTrace]
  refine ⟨47352909432980889283685465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126274425154615704756494573 47352909432980889283685465)
  ·
    refine ⟨35514682074735666962764099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47352909432980889283685465 35514682074735666962764099)
    ·
      refine ⟨53272023112103500444146149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35514682074735666962764099 53272023112103500444146149)
      ·
        refine ⟨9988504333519406333277403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53272023112103500444146149 9988504333519406333277403)
        ·
          refine ⟨14982756500279109499916105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9988504333519406333277403 14982756500279109499916105)
          ·
            refine ⟨11237067375209332124937079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14982756500279109499916105 11237067375209332124937079)
            ·
              refine ⟨16855601062813998187405619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11237067375209332124937079 16855601062813998187405619)
              ·
                refine ⟨25283401594220997281108429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16855601062813998187405619 25283401594220997281108429)
                ·
                  refine ⟨9481275597832873980415661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25283401594220997281108429 9481275597832873980415661)
                  ·
                    refine ⟨3555478349187327742655873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9481275597832873980415661 3555478349187327742655873)
                    ·
                      refine ⟨2666608761890495806991905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555478349187327742655873 2666608761890495806991905)
                      ·
                        rfl

theorem cell23_5193202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5193202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193202 prefixEnd_5193202 := by exact prefixLift 5193202
  have htrace : WordTrace (prefixWord ++ tailWord_5193202) baseStart_5193202 baseEnd_5193202 := by
    simpa [prefixWord, tailWord_5193202, baseEnd_5193202] using wordTrace_append hprefix tailTrace_5193202
  have hstable : (prefixWord ++ tailWord_5193202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193202).length < 2 ^ (prefixWord ++ tailWord_5193202).sum := by decide
  have hdescent : baseEnd_5193202 < baseStart_5193202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193211 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4]
def baseStart_5193211 : Nat := 118140960795 + 5193211 * 2 ^ 59
def prefixEnd_5193211 : Nat := 4983230072969 + 3 ^ 40 * 5193211 * 2
def baseEnd_5193211 : Nat := 2666613383216386271779363

theorem tailTrace_5193211 : CollatzResearch.WordTrace tailWord_5193211 prefixEnd_5193211 2666613383216386271779363 := by
  unfold tailWord_5193211
  simp only [CollatzResearch.WordTrace]
  refine ⟨189411965988890951671819487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126274643992593967781212991 189411965988890951671819487)
  ·
    refine ⟨284117948983336427507729231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189411965988890951671819487 284117948983336427507729231)
    ·
      refine ⟨426176923475004641261593847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284117948983336427507729231 426176923475004641261593847)
      ·
        refine ⟨639265385212506961892390771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426176923475004641261593847 639265385212506961892390771)
        ·
          refine ⟨958898077818760442838586157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639265385212506961892390771 958898077818760442838586157)
          ·
            refine ⟨359586779182035166064469809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 958898077818760442838586157 359586779182035166064469809)
            ·
              refine ⟨269690084386526374548352357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359586779182035166064469809 269690084386526374548352357)
              ·
                refine ⟨50566890822473695227816067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269690084386526374548352357 50566890822473695227816067)
                ·
                  refine ⟨75850336233710542841724101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50566890822473695227816067 75850336233710542841724101)
                  ·
                    refine ⟨14221938043820726782823269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75850336233710542841724101 14221938043820726782823269)
                    ·
                      refine ⟨2666613383216386271779363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14221938043820726782823269 2666613383216386271779363)
                      ·
                        rfl

theorem cell23_5193211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_5193211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193211 prefixEnd_5193211 := by exact prefixLift 5193211
  have htrace : WordTrace (prefixWord ++ tailWord_5193211) baseStart_5193211 baseEnd_5193211 := by
    simpa [prefixWord, tailWord_5193211, baseEnd_5193211] using wordTrace_append hprefix tailTrace_5193211
  have hstable : (prefixWord ++ tailWord_5193211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193211).length < 2 ^ (prefixWord ++ tailWord_5193211).sum := by decide
  have hdescent : baseEnd_5193211 < baseStart_5193211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193215 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 4, 2, 2]
def baseStart_5193215 : Nat := 118140960795 + 5193215 * 2 ^ 59
def prefixEnd_5193215 : Nat := 4983230072969 + 3 ^ 40 * 5193215 * 2
def baseEnd_5193215 : Nat := 2666615437139004256129345

theorem tailTrace_5193215 : CollatzResearch.WordTrace tailWord_5193215 prefixEnd_5193215 2666615437139004256129345 := by
  unfold tailWord_5193215
  simp only [CollatzResearch.WordTrace]
  refine ⟨189412111880876460354965099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126274741253917640236643399 189412111880876460354965099)
  ·
    refine ⟨284118167821314690532447649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189412111880876460354965099 284118167821314690532447649)
    ·
      refine ⟨213088625865986017899335737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284118167821314690532447649 213088625865986017899335737)
      ·
        refine ⟨159816469399489513424501803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213088625865986017899335737 159816469399489513424501803)
        ·
          refine ⟨239724704099234270136752705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159816469399489513424501803 239724704099234270136752705)
          ·
            refine ⟨179793528074425702602564529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239724704099234270136752705 179793528074425702602564529)
            ·
              refine ⟨134845146055819276951923397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179793528074425702602564529 134845146055819276951923397)
              ·
                refine ⟨25283464885466114428485637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134845146055819276951923397 25283464885466114428485637)
                ·
                  refine ⟨4740649666024896455341057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25283464885466114428485637 4740649666024896455341057)
                  ·
                    refine ⟨3555487249518672341505793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4740649666024896455341057 3555487249518672341505793)
                    ·
                      refine ⟨2666615437139004256129345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555487249518672341505793 2666615437139004256129345)
                      ·
                        rfl

theorem cell23_5193215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_5193215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193215 prefixEnd_5193215 := by exact prefixLift 5193215
  have htrace : WordTrace (prefixWord ++ tailWord_5193215) baseStart_5193215 baseEnd_5193215 := by
    simpa [prefixWord, tailWord_5193215, baseEnd_5193215] using wordTrace_append hprefix tailTrace_5193215
  have hstable : (prefixWord ++ tailWord_5193215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193215).length < 2 ^ (prefixWord ++ tailWord_5193215).sum := by decide
  have hdescent : baseEnd_5193215 < baseStart_5193215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193315 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 3, 4]
def baseStart_5193315 : Nat := 118140960795 + 5193315 * 2 ^ 59
def prefixEnd_5193315 : Nat := 4983230072969 + 3 ^ 40 * 5193315 * 2
def baseEnd_5193315 : Nat := 888888928401484621626295

theorem tailTrace_5193315 : CollatzResearch.WordTrace tailWord_5193315 prefixEnd_5193315 888888928401484621626295 := by
  unfold tailWord_5193315
  simp only [CollatzResearch.WordTrace]
  refine ⟨189415759180514177433605399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126277172787009451622403599 189415759180514177433605399)
  ·
    refine ⟨284123638770771266150408099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189415759180514177433605399 284123638770771266150408099)
    ·
      refine ⟨426185458156156899225612149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284123638770771266150408099 426185458156156899225612149)
      ·
        refine ⟨39954886702139709302401139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 426185458156156899225612149 39954886702139709302401139)
        ·
          refine ⟨59932330053209563953601709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39954886702139709302401139 59932330053209563953601709)
          ·
            refine ⟨22474623769953586482600641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59932330053209563953601709 22474623769953586482600641)
            ·
              refine ⟨16855967827465189861950481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22474623769953586482600641 16855967827465189861950481)
              ·
                refine ⟨12641975870598892396462861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16855967827465189861950481 12641975870598892396462861)
                ·
                  refine ⟨4740740951474584648673573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12641975870598892396462861 4740740951474584648673573)
                  ·
                    refine ⟨888888928401484621626295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4740740951474584648673573 888888928401484621626295)
                    ·
                      rfl

theorem cell23_5193315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 4].length) (baseStart_5193315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193315 prefixEnd_5193315 := by exact prefixLift 5193315
  have htrace : WordTrace (prefixWord ++ tailWord_5193315) baseStart_5193315 baseEnd_5193315 := by
    simpa [prefixWord, tailWord_5193315, baseEnd_5193315] using wordTrace_append hprefix tailTrace_5193315
  have hstable : (prefixWord ++ tailWord_5193315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193315).length < 2 ^ (prefixWord ++ tailWord_5193315).sum := by decide
  have hdescent : baseEnd_5193315 < baseStart_5193315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193328 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 8]
def baseStart_5193328 : Nat := 118140960795 + 5193328 * 2 ^ 59
def prefixEnd_5193328 : Nat := 4983230072969 + 3 ^ 40 * 5193328 * 2
def baseEnd_5193328 : Nat := 296297051161440257112925

theorem tailTrace_5193328 : CollatzResearch.WordTrace tailWord_5193328 prefixEnd_5193328 296297051161440257112925 := by
  unfold tailWord_5193328
  simp only [CollatzResearch.WordTrace]
  refine ⟨94708116664733540326914319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126277488886311387102552425 94708116664733540326914319)
  ·
    refine ⟨142062174997100310490371479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94708116664733540326914319 142062174997100310490371479)
    ·
      refine ⟨213093262495650465735557219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142062174997100310490371479 213093262495650465735557219)
      ·
        refine ⟨319639893743475698603335829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213093262495650465735557219 319639893743475698603335829)
        ·
          refine ⟨14983120019225423372031367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 319639893743475698603335829 14983120019225423372031367)
          ·
            refine ⟨22474680028838135058047051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14983120019225423372031367 22474680028838135058047051)
            ·
              refine ⟨33712020043257202587070577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22474680028838135058047051 33712020043257202587070577)
              ·
                refine ⟨25284015032442901940302933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33712020043257202587070577 25284015032442901940302933)
                ·
                  refine ⟨296297051161440257112925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25284015032442901940302933 296297051161440257112925)
                  ·
                    rfl

theorem cell23_5193328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_5193328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193328 prefixEnd_5193328 := by exact prefixLift 5193328
  have htrace : WordTrace (prefixWord ++ tailWord_5193328) baseStart_5193328 baseEnd_5193328 := by
    simpa [prefixWord, tailWord_5193328, baseEnd_5193328] using wordTrace_append hprefix tailTrace_5193328
  have hstable : (prefixWord ++ tailWord_5193328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193328).length < 2 ^ (prefixWord ++ tailWord_5193328).sum := by decide
  have hdescent : baseEnd_5193328 < baseStart_5193328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193349 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_5193349 : Nat := 118140960795 + 5193349 * 2 ^ 59
def prefixEnd_5193349 : Nat := 4983230072969 + 3 ^ 40 * 5193349 * 2
def baseEnd_5193349 : Nat := 888894747848902243951243

theorem tailTrace_5193349 : CollatzResearch.WordTrace tailWord_5193349 prefixEnd_5193349 888894747848902243951243 := by
  unfold tailWord_5193349
  simp only [CollatzResearch.WordTrace]
  refine ⟨189416999262391001240343101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126277999508260667493562067 189416999262391001240343101)
  ·
    refine ⟨71031374723396625465128663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189416999262391001240343101 71031374723396625465128663)
    ·
      refine ⟨106547062085094938197692995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71031374723396625465128663 106547062085094938197692995)
      ·
        refine ⟨159820593127642407296539493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106547062085094938197692995 159820593127642407296539493)
        ·
          refine ⟨29966361211432951368101155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159820593127642407296539493 29966361211432951368101155)
          ·
            refine ⟨44949541817149427052151733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29966361211432951368101155 44949541817149427052151733)
            ·
              refine ⟨4214019545357758786139225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44949541817149427052151733 4214019545357758786139225)
              ·
                refine ⟨3160514659018319089604419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4214019545357758786139225 3160514659018319089604419)
                ·
                  refine ⟨4740771988527478634406629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160514659018319089604419 4740771988527478634406629)
                  ·
                    refine ⟨888894747848902243951243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4740771988527478634406629 888894747848902243951243)
                    ·
                      rfl

theorem cell23_5193349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_5193349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193349 prefixEnd_5193349 := by exact prefixLift 5193349
  have htrace : WordTrace (prefixWord ++ tailWord_5193349) baseStart_5193349 baseEnd_5193349 := by
    simpa [prefixWord, tailWord_5193349, baseEnd_5193349] using wordTrace_append hprefix tailTrace_5193349
  have hstable : (prefixWord ++ tailWord_5193349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193349).length < 2 ^ (prefixWord ++ tailWord_5193349).sum := by decide
  have hdescent : baseEnd_5193349 < baseStart_5193349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193362 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_5193362 : Nat := 118140960795 + 5193362 * 2 ^ 59
def prefixEnd_5193362 : Nat := 4983230072969 + 3 ^ 40 * 5193362 * 2
def baseEnd_5193362 : Nat := 296298990977246131221241

theorem tailTrace_5193362 : CollatzResearch.WordTrace tailWord_5193362 prefixEnd_5193362 296298990977246131221241 := by
  unfold tailWord_5193362
  simp only [CollatzResearch.WordTrace]
  refine ⟨47354368352835976115141585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126278315607562602973710893 47354368352835976115141585)
  ·
    refine ⟨35515776264626982086356189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47354368352835976115141585 35515776264626982086356189)
    ·
      refine ⟨13318416099235118282383571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35515776264626982086356189 13318416099235118282383571)
      ·
        refine ⟨19977624148852677423575357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13318416099235118282383571 19977624148852677423575357)
        ·
          refine ⟨7491609055819754033840759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19977624148852677423575357 7491609055819754033840759)
          ·
            refine ⟨11237413583729631050761139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7491609055819754033840759 11237413583729631050761139)
            ·
              refine ⟨16856120375594446576141709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11237413583729631050761139 16856120375594446576141709)
              ·
                refine ⟨6321045140847917466053141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16856120375594446576141709 6321045140847917466053141)
                ·
                  refine ⟨296298990977246131221241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6321045140847917466053141 296298990977246131221241)
                  ·
                    rfl

theorem cell23_5193362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_5193362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193362 prefixEnd_5193362 := by exact prefixLift 5193362
  have htrace : WordTrace (prefixWord ++ tailWord_5193362) baseStart_5193362 baseEnd_5193362 := by
    simpa [prefixWord, tailWord_5193362, baseEnd_5193362] using wordTrace_append hprefix tailTrace_5193362
  have hstable : (prefixWord ++ tailWord_5193362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193362).length < 2 ^ (prefixWord ++ tailWord_5193362).sum := by decide
  have hdescent : baseEnd_5193362 < baseStart_5193362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193365 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_5193365 : Nat := 118140960795 + 5193365 * 2 ^ 59
def prefixEnd_5193365 : Nat := 4983230072969 + 3 ^ 40 * 5193365 * 2
def baseEnd_5193365 : Nat := 2666692459237178669253655

theorem tailTrace_5193365 : CollatzResearch.WordTrace tailWord_5193365 prefixEnd_5193365 2666692459237178669253655 := by
  unfold tailWord_5193365
  simp only [CollatzResearch.WordTrace]
  refine ⟨189417582830333035972925549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126278388553555357315283699 189417582830333035972925549)
  ·
    refine ⟨71031593561374888489847081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189417582830333035972925549 71031593561374888489847081)
    ·
      refine ⟨53273695171031166367385311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71031593561374888489847081 53273695171031166367385311)
      ·
        refine ⟨79910542756546749551077967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53273695171031166367385311 79910542756546749551077967)
        ·
          refine ⟨119865814134820124326616951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79910542756546749551077967 119865814134820124326616951)
          ·
            refine ⟨179798721202230186489925427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119865814134820124326616951 179798721202230186489925427)
            ·
              refine ⟨269698081803345279734888141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179798721202230186489925427 269698081803345279734888141)
              ·
                refine ⟨101136780676254479900583053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269698081803345279734888141 101136780676254479900583053)
                ·
                  refine ⟨37926292753595429962718645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101136780676254479900583053 37926292753595429962718645)
                  ·
                    refine ⟨3555589945649571559004873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37926292753595429962718645 3555589945649571559004873)
                    ·
                      refine ⟨2666692459237178669253655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555589945649571559004873 2666692459237178669253655)
                      ·
                        rfl

theorem cell23_5193365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_5193365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193365 prefixEnd_5193365 := by exact prefixLift 5193365
  have htrace : WordTrace (prefixWord ++ tailWord_5193365) baseStart_5193365 baseEnd_5193365 := by
    simpa [prefixWord, tailWord_5193365, baseEnd_5193365] using wordTrace_append hprefix tailTrace_5193365
  have hstable : (prefixWord ++ tailWord_5193365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193365).length < 2 ^ (prefixWord ++ tailWord_5193365).sum := by decide
  have hdescent : baseEnd_5193365 < baseStart_5193365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193406 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_5193406 : Nat := 118140960795 + 5193406 * 2 ^ 59
def prefixEnd_5193406 : Nat := 4983230072969 + 3 ^ 40 * 5193406 * 2
def baseEnd_5193406 : Nat := 2666713511944013008840967

theorem tailTrace_5193406 : CollatzResearch.WordTrace tailWord_5193406 prefixEnd_5193406 2666713511944013008840967 := by
  unfold tailWord_5193406
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677384777898062496896009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126279385482122999983445381 23677384777898062496896009)
  ·
    refine ⟨17758038583423546872672007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23677384777898062496896009 17758038583423546872672007)
    ·
      refine ⟨26637057875135320309008011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17758038583423546872672007 26637057875135320309008011)
      ·
        refine ⟨39955586812702980463512017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26637057875135320309008011 39955586812702980463512017)
        ·
          refine ⟨29966690109527235347634013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39955586812702980463512017 29966690109527235347634013)
          ·
            refine ⟨11237508791072713255362755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29966690109527235347634013 11237508791072713255362755)
            ·
              refine ⟨16856263186609069883044133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11237508791072713255362755 16856263186609069883044133)
              ·
                refine ⟨3160549347489200603070775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16856263186609069883044133 3160549347489200603070775)
                ·
                  refine ⟨4740824021233800904606163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160549347489200603070775 4740824021233800904606163)
                  ·
                    refine ⟨7111236031850701356909245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4740824021233800904606163 7111236031850701356909245)
                    ·
                      refine ⟨2666713511944013008840967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7111236031850701356909245 2666713511944013008840967)
                      ·
                        rfl

theorem cell23_5193406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_5193406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193406 prefixEnd_5193406 := by exact prefixLift 5193406
  have htrace : WordTrace (prefixWord ++ tailWord_5193406) baseStart_5193406 baseEnd_5193406 := by
    simpa [prefixWord, tailWord_5193406, baseEnd_5193406] using wordTrace_append hprefix tailTrace_5193406
  have hstable : (prefixWord ++ tailWord_5193406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193406).length < 2 ^ (prefixWord ++ tailWord_5193406).sum := by decide
  have hdescent : baseEnd_5193406 < baseStart_5193406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193415 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_5193415 : Nat := 118140960795 + 5193415 * 2 ^ 59
def prefixEnd_5193415 : Nat := 4983230072969 + 3 ^ 40 * 5193415 * 2
def baseEnd_5193415 : Nat := 2666718133269903473628425

theorem tailTrace_5193415 : CollatzResearch.WordTrace tailWord_5193415 prefixEnd_5193415 2666718133269903473628425 := by
  unfold tailWord_5193415
  simp only [CollatzResearch.WordTrace]
  refine ⟨189419406480151894512245699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126279604320101263008163799 189419406480151894512245699)
  ·
    refine ⟨284129109720227841768368549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189419406480151894512245699 284129109720227841768368549)
    ·
      refine ⟨53274208072542720331569103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284129109720227841768368549 53274208072542720331569103)
      ·
        refine ⟨79911312108814080497353655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53274208072542720331569103 79911312108814080497353655)
        ·
          refine ⟨119866968163221120746030483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79911312108814080497353655 119866968163221120746030483)
          ·
            refine ⟨179800452244831681119045725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119866968163221120746030483 179800452244831681119045725)
            ·
              refine ⟨67425169591811880419642147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179800452244831681119045725 67425169591811880419642147)
              ·
                refine ⟨101137754387717820629463221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67425169591811880419642147 101137754387717820629463221)
                ·
                  refine ⟨9481664473848545684012177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101137754387717820629463221 9481664473848545684012177)
                  ·
                    refine ⟨7111248355386409263009133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9481664473848545684012177 7111248355386409263009133)
                    ·
                      refine ⟨2666718133269903473628425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7111248355386409263009133 2666718133269903473628425)
                      ·
                        rfl

theorem cell23_5193415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_5193415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193415 prefixEnd_5193415 := by exact prefixLift 5193415
  have htrace : WordTrace (prefixWord ++ tailWord_5193415) baseStart_5193415 baseEnd_5193415 := by
    simpa [prefixWord, tailWord_5193415, baseEnd_5193415] using wordTrace_append hprefix tailTrace_5193415
  have hstable : (prefixWord ++ tailWord_5193415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193415).length < 2 ^ (prefixWord ++ tailWord_5193415).sum := by decide
  have hdescent : baseEnd_5193415 < baseStart_5193415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193422 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_5193422 : Nat := 118140960795 + 5193422 * 2 ^ 59
def prefixEnd_5193422 : Nat := 4983230072969 + 3 ^ 40 * 5193422 * 2
def baseEnd_5193422 : Nat := 888907242544828315413631

theorem tailTrace_5193422 : CollatzResearch.WordTrace tailWord_5193422 prefixEnd_5193422 888907242544828315413631 := by
  unfold tailWord_5193422
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677457723890816838468815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126279774527417689805167013 23677457723890816838468815)
  ·
    refine ⟨35516186585836225257703223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23677457723890816838468815 35516186585836225257703223)
    ·
      refine ⟨53274279878754337886554835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35516186585836225257703223 53274279878754337886554835)
      ·
        refine ⟨79911419818131506829832253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53274279878754337886554835 79911419818131506829832253)
        ·
          refine ⟨29966782431799315061187095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79911419818131506829832253 29966782431799315061187095)
          ·
            refine ⟨44950173647698972591780643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29966782431799315061187095 44950173647698972591780643)
            ·
              refine ⟨67425260471548458887670965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44950173647698972591780643 67425260471548458887670965)
              ·
                refine ⟨6321118169207668020719153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67425260471548458887670965 6321118169207668020719153)
                ·
                  refine ⟨4740838626905751015539365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321118169207668020719153 4740838626905751015539365)
                  ·
                    refine ⟨888907242544828315413631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4740838626905751015539365 888907242544828315413631)
                    ·
                      rfl

theorem cell23_5193422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_5193422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193422 prefixEnd_5193422 := by exact prefixLift 5193422
  have htrace : WordTrace (prefixWord ++ tailWord_5193422) baseStart_5193422 baseEnd_5193422 := by
    simpa [prefixWord, tailWord_5193422, baseEnd_5193422] using wordTrace_append hprefix tailTrace_5193422
  have hstable : (prefixWord ++ tailWord_5193422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193422).length < 2 ^ (prefixWord ++ tailWord_5193422).sum := by decide
  have hdescent : baseEnd_5193422 < baseStart_5193422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193425 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_5193425 : Nat := 118140960795 + 5193425 * 2 ^ 59
def prefixEnd_5193425 : Nat := 4983230072969 + 3 ^ 40 * 5193425 * 2
def baseEnd_5193425 : Nat := 2666723268076448434503379

theorem tailTrace_5193425 : CollatzResearch.WordTrace tailWord_5193425 prefixEnd_5193425 2666723268076448434503379 := by
  unfold tailWord_5193425
  simp only [CollatzResearch.WordTrace]
  refine ⟨189419771210115666220109729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126279847473410444146739819 189419771210115666220109729)
  ·
    refine ⟨142064828407586749665082297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189419771210115666220109729 142064828407586749665082297)
    ·
      refine ⟨106548621305690062248811723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142064828407586749665082297 106548621305690062248811723)
      ·
        refine ⟨159822931958535093373217585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106548621305690062248811723 159822931958535093373217585)
        ·
          refine ⟨119867198968901320029913189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159822931958535093373217585 119867198968901320029913189)
          ·
            refine ⟨22475099806668997505608723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119867198968901320029913189 22475099806668997505608723)
            ·
              refine ⟨33712649710003496258413085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22475099806668997505608723 33712649710003496258413085)
              ·
                refine ⟨12642243641251311096904907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33712649710003496258413085 12642243641251311096904907)
                ·
                  refine ⟨18963365461876966645357361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12642243641251311096904907 18963365461876966645357361)
                  ·
                    refine ⟨14222524096407724984018021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18963365461876966645357361 14222524096407724984018021)
                    ·
                      refine ⟨2666723268076448434503379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14222524096407724984018021 2666723268076448434503379)
                      ·
                        rfl

theorem cell23_5193425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_5193425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193425 prefixEnd_5193425 := by exact prefixLift 5193425
  have htrace : WordTrace (prefixWord ++ tailWord_5193425) baseStart_5193425 baseEnd_5193425 := by
    simpa [prefixWord, tailWord_5193425, baseEnd_5193425] using wordTrace_append hprefix tailTrace_5193425
  have hstable : (prefixWord ++ tailWord_5193425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193425).length < 2 ^ (prefixWord ++ tailWord_5193425).sum := by decide
  have hdescent : baseEnd_5193425 < baseStart_5193425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193432 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_5193432 : Nat := 118140960795 + 5193432 * 2 ^ 59
def prefixEnd_5193432 : Nat := 4983230072969 + 3 ^ 40 * 5193432 * 2
def baseEnd_5193432 : Nat := 2666726862441029907115847

theorem tailTrace_5193432 : CollatzResearch.WordTrace tailWord_5193432 prefixEnd_5193432 2666726862441029907115847 := by
  unfold tailWord_5193432
  simp only [CollatzResearch.WordTrace]
  refine ⟨94710013260545153207807275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126280017680726870943743033 94710013260545153207807275)
  ·
    refine ⟨142065019890817729811710913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94710013260545153207807275 142065019890817729811710913)
    ·
      refine ⟨106548764918113297358783185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142065019890817729811710913 106548764918113297358783185)
      ·
        refine ⟨79911573688584973019087389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106548764918113297358783185 79911573688584973019087389)
        ·
          refine ⟨29966840133219364882157771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79911573688584973019087389 29966840133219364882157771)
          ·
            refine ⟨44950260199829047323236657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29966840133219364882157771 44950260199829047323236657)
            ·
              refine ⟨33712695149871785492427493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44950260199829047323236657 33712695149871785492427493)
              ·
                refine ⟨6321130340600959779830155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33712695149871785492427493 6321130340600959779830155)
                ·
                  refine ⟨9481695510901439669745233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6321130340600959779830155 9481695510901439669745233)
                  ·
                    refine ⟨7111271633176079752308925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9481695510901439669745233 7111271633176079752308925)
                    ·
                      refine ⟨2666726862441029907115847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7111271633176079752308925 2666726862441029907115847)
                      ·
                        rfl

theorem cell23_5193432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_5193432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193432 prefixEnd_5193432 := by exact prefixLift 5193432
  have htrace : WordTrace (prefixWord ++ tailWord_5193432) baseStart_5193432 baseEnd_5193432 := by
    simpa [prefixWord, tailWord_5193432, baseEnd_5193432] using wordTrace_append hprefix tailTrace_5193432
  have hstable : (prefixWord ++ tailWord_5193432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193432).length < 2 ^ (prefixWord ++ tailWord_5193432).sum := by decide
  have hdescent : baseEnd_5193432 < baseStart_5193432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193505 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5193505 : Nat := 118140960795 + 5193505 * 2 ^ 59
def prefixEnd_5193505 : Nat := 4983230072969 + 3 ^ 40 * 5193505 * 2
def baseEnd_5193505 : Nat := 2666764346528808121503011

theorem tailTrace_5193505 : CollatzResearch.WordTrace tailWord_5193505 prefixEnd_5193505 2666764346528808121503011 := by
  unfold tailWord_5193505
  simp only [CollatzResearch.WordTrace]
  refine ⟨189422689049825839883021969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126281792699883893255347979 189422689049825839883021969)
  ·
    refine ⟨142067016787369379912266477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189422689049825839883021969 142067016787369379912266477)
    ·
      refine ⟨53275131295263517467099929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142067016787369379912266477 53275131295263517467099929)
      ·
        refine ⟨39956348471447638100324947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53275131295263517467099929 39956348471447638100324947)
        ·
          refine ⟨59934522707171457150487421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39956348471447638100324947 59934522707171457150487421)
          ·
            refine ⟨22475446015189296431432783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59934522707171457150487421 22475446015189296431432783)
            ·
              refine ⟨33713169022783944647149175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22475446015189296431432783 33713169022783944647149175)
              ·
                refine ⟨50569753534175916970723763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33713169022783944647149175 50569753534175916970723763)
                ·
                  refine ⟨75854630301263875456085645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50569753534175916970723763 75854630301263875456085645)
                  ·
                    refine ⟨28445486362973953296032117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75854630301263875456085645 28445486362973953296032117)
                    ·
                      refine ⟨2666764346528808121503011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28445486362973953296032117 2666764346528808121503011)
                      ·
                        rfl

theorem cell23_5193505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5193505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193505 prefixEnd_5193505 := by exact prefixLift 5193505
  have htrace : WordTrace (prefixWord ++ tailWord_5193505) baseStart_5193505 baseEnd_5193505 := by
    simpa [prefixWord, tailWord_5193505, baseEnd_5193505] using wordTrace_append hprefix tailTrace_5193505
  have hstable : (prefixWord ++ tailWord_5193505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193505).length < 2 ^ (prefixWord ++ tailWord_5193505).sum := by decide
  have hdescent : baseEnd_5193505 < baseStart_5193505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193636 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_5193636 : Nat := 118140960795 + 5193636 * 2 ^ 59
def prefixEnd_5193636 : Nat := 4983230072969 + 3 ^ 40 * 5193636 * 2
def baseEnd_5193636 : Nat := 888943870831515702988303

theorem tailTrace_5193636 : CollatzResearch.WordTrace tailWord_5193636 prefixEnd_5193636 888943870831515702988303 := by
  unfold tailWord_5193636
  simp only [CollatzResearch.WordTrace]
  refine ⟨94713733506175624628020381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126284978008234166170693841 94713733506175624628020381)
  ·
    refine ⟨35517650064815859235507643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94713733506175624628020381 35517650064815859235507643)
    ·
      refine ⟨53276475097223788853261465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35517650064815859235507643 53276475097223788853261465)
      ·
        refine ⟨39957356322917841639946099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53276475097223788853261465 39957356322917841639946099)
        ·
          refine ⟨59936034484376762459919149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39957356322917841639946099 59936034484376762459919149)
          ·
            refine ⟨22476012931641285922469681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59936034484376762459919149 22476012931641285922469681)
            ·
              refine ⟨16857009698730964441852261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22476012931641285922469681 16857009698730964441852261)
              ·
                refine ⟨3160689318512055832847299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16857009698730964441852261 3160689318512055832847299)
                ·
                  refine ⟨4741033977768083749270949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3160689318512055832847299 4741033977768083749270949)
                  ·
                    refine ⟨888943870831515702988303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741033977768083749270949 888943870831515702988303)
                    ·
                      rfl

theorem cell23_5193636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_5193636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193636 prefixEnd_5193636 := by exact prefixLift 5193636
  have htrace : WordTrace (prefixWord ++ tailWord_5193636) baseStart_5193636 baseEnd_5193636 := by
    simpa [prefixWord, tailWord_5193636, baseEnd_5193636] using wordTrace_append hprefix tailTrace_5193636
  have hstable : (prefixWord ++ tailWord_5193636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193636).length < 2 ^ (prefixWord ++ tailWord_5193636).sum := by decide
  have hdescent : baseEnd_5193636 < baseStart_5193636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193712 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_5193712 : Nat := 118140960795 + 5193712 * 2 ^ 59
def prefixEnd_5193712 : Nat := 4983230072969 + 3 ^ 40 * 5193712 * 2
def baseEnd_5193712 : Nat := 2666870637024288811614559

theorem tailTrace_5193712 : CollatzResearch.WordTrace tailWord_5193712 prefixEnd_5193712 2666870637024288811614559 := by
  unfold tailWord_5193712
  simp only [CollatzResearch.WordTrace]
  refine ⟨94715119480037957117903695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126286825973383942823871593 94715119480037957117903695)
  ·
    refine ⟨142072679220056935676855543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94715119480037957117903695 142072679220056935676855543)
    ·
      refine ⟨213109018830085403515283315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142072679220056935676855543 213109018830085403515283315)
      ·
        refine ⟨319663528245128105272924973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213109018830085403515283315 319663528245128105272924973)
        ·
          refine ⟨119873823091923039477346865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319663528245128105272924973 119873823091923039477346865)
          ·
            refine ⟨89905367318942279608010149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119873823091923039477346865 89905367318942279608010149)
            ·
              refine ⟨16857256372301677426501903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89905367318942279608010149 16857256372301677426501903)
              ·
                refine ⟨25285884558452516139752855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16857256372301677426501903 25285884558452516139752855)
                ·
                  refine ⟨37928826837678774209629283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25285884558452516139752855 37928826837678774209629283)
                  ·
                    refine ⟨56893240256518161314443925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37928826837678774209629283 56893240256518161314443925)
                    ·
                      refine ⟨2666870637024288811614559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56893240256518161314443925 2666870637024288811614559)
                      ·
                        rfl

theorem cell23_5193712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_5193712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193712 prefixEnd_5193712 := by exact prefixLift 5193712
  have htrace : WordTrace (prefixWord ++ tailWord_5193712) baseStart_5193712 baseEnd_5193712 := by
    simpa [prefixWord, tailWord_5193712, baseEnd_5193712] using wordTrace_append hprefix tailTrace_5193712
  have hstable : (prefixWord ++ tailWord_5193712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193712).length < 2 ^ (prefixWord ++ tailWord_5193712).sum := by decide
  have hdescent : baseEnd_5193712 < baseStart_5193712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193713 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 1, 5]
def baseStart_5193713 : Nat := 118140960795 + 5193713 * 2 ^ 59
def prefixEnd_5193713 : Nat := 4983230072969 + 3 ^ 40 * 5193713 * 2
def baseEnd_5193713 : Nat := 888957050168314435900685

theorem tailTrace_5193713 : CollatzResearch.WordTrace tailWord_5193713 prefixEnd_5193713 888957050168314435900685 := by
  unfold tailWord_5193713
  simp only [CollatzResearch.WordTrace]
  refine ⟨189430275433072291406593793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126286850288714860937729195 189430275433072291406593793)
  ·
    refine ⟨142072706574804218554945345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189430275433072291406593793 142072706574804218554945345)
    ·
      refine ⟨106554529931103163916209009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142072706574804218554945345 106554529931103163916209009)
      ·
        refine ⟨79915897448327372937156757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106554529931103163916209009 79915897448327372937156757)
        ·
          refine ⟨3746057692890345606429223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79915897448327372937156757 3746057692890345606429223)
          ·
            refine ⟨5619086539335518409643835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746057692890345606429223 5619086539335518409643835)
            ·
              refine ⟨8428629809003277614465753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619086539335518409643835 8428629809003277614465753)
              ·
                refine ⟨6321472356752458210849315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8428629809003277614465753 6321472356752458210849315)
                ·
                  refine ⟨9482208535128687316273973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6321472356752458210849315 9482208535128687316273973)
                  ·
                    refine ⟨888957050168314435900685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9482208535128687316273973 888957050168314435900685)
                    ·
                      rfl

theorem cell23_5193713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_5193713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193713 prefixEnd_5193713 := by exact prefixLift 5193713
  have htrace : WordTrace (prefixWord ++ tailWord_5193713) baseStart_5193713 baseEnd_5193713 := by
    simpa [prefixWord, tailWord_5193713, baseEnd_5193713] using wordTrace_append hprefix tailTrace_5193713
  have hstable : (prefixWord ++ tailWord_5193713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193713).length < 2 ^ (prefixWord ++ tailWord_5193713).sum := by decide
  have hdescent : baseEnd_5193713 < baseStart_5193713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193726 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_5193726 : Nat := 118140960795 + 5193726 * 2 ^ 59
def prefixEnd_5193726 : Nat := 4983230072969 + 3 ^ 40 * 5193726 * 2
def baseEnd_5193726 : Nat := 888959275251150585613165

theorem tailTrace_5193726 : CollatzResearch.WordTrace tailWord_5193726 prefixEnd_5193726 888959275251150585613165 := by
  unfold tailWord_5193726
  simp only [CollatzResearch.WordTrace]
  refine ⟨23678843697753149328352129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126287166388016796417878021 23678843697753149328352129)
  ·
    refine ⟨17759132773314861996264097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23678843697753149328352129 17759132773314861996264097)
    ·
      refine ⟨13319349579986146497198073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17759132773314861996264097 13319349579986146497198073)
      ·
        refine ⟨9989512184989609872898555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13319349579986146497198073 9989512184989609872898555)
        ·
          refine ⟨14984268277484414809347833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9989512184989609872898555 14984268277484414809347833)
          ·
            refine ⟨11238201208113311107010875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14984268277484414809347833 11238201208113311107010875)
            ·
              refine ⟨16857301812169966660516313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11238201208113311107010875 16857301812169966660516313)
              ·
                refine ⟨12642976359127474995387235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16857301812169966660516313 12642976359127474995387235)
                ·
                  refine ⟨18964464538691212493080853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12642976359127474995387235 18964464538691212493080853)
                  ·
                    refine ⟨888959275251150585613165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18964464538691212493080853 888959275251150585613165)
                    ·
                      rfl

theorem cell23_5193726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_5193726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193726 prefixEnd_5193726 := by exact prefixLift 5193726
  have htrace : WordTrace (prefixWord ++ tailWord_5193726) baseStart_5193726 baseEnd_5193726 := by
    simpa [prefixWord, tailWord_5193726, baseEnd_5193726] using wordTrace_append hprefix tailTrace_5193726
  have hstable : (prefixWord ++ tailWord_5193726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193726).length < 2 ^ (prefixWord ++ tailWord_5193726).sum := by decide
  have hdescent : baseEnd_5193726 < baseStart_5193726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193729 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_5193729 : Nat := 118140960795 + 5193729 * 2 ^ 59
def prefixEnd_5193729 : Nat := 4983230072969 + 3 ^ 40 * 5193729 * 2
def baseEnd_5193729 : Nat := 2666879366195415245101981

theorem tailTrace_5193729 : CollatzResearch.WordTrace tailWord_5193729 prefixEnd_5193729 2666879366195415245101981 := by
  unfold tailWord_5193729
  simp only [CollatzResearch.WordTrace]
  refine ⟨189430859001014326139176241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126287239334009550759450827 189430859001014326139176241)
  ·
    refine ⟨142073144250760744604382181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189430859001014326139176241 142073144250760744604382181)
    ·
      refine ⟨26638714547017639613321659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142073144250760744604382181 26638714547017639613321659)
      ·
        refine ⟨39958071820526459419982489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26638714547017639613321659 39958071820526459419982489)
        ·
          refine ⟨29968553865394844564986867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39958071820526459419982489 29968553865394844564986867)
          ·
            refine ⟨44952830798092266847480301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29968553865394844564986867 44952830798092266847480301)
            ·
              refine ⟨16857311549284600067805113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44952830798092266847480301 16857311549284600067805113)
              ·
                refine ⟨12642983661963450050853835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16857311549284600067805113 12642983661963450050853835)
                ·
                  refine ⟨18964475492945175076280753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12642983661963450050853835 18964475492945175076280753)
                  ·
                    refine ⟨14223356619708881307210565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18964475492945175076280753 14223356619708881307210565)
                    ·
                      refine ⟨2666879366195415245101981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14223356619708881307210565 2666879366195415245101981)
                      ·
                        rfl

theorem cell23_5193729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_5193729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193729 prefixEnd_5193729 := by exact prefixLift 5193729
  have htrace : WordTrace (prefixWord ++ tailWord_5193729) baseStart_5193729 baseEnd_5193729 := by
    simpa [prefixWord, tailWord_5193729, baseEnd_5193729] using wordTrace_append hprefix tailTrace_5193729
  have hstable : (prefixWord ++ tailWord_5193729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193729).length < 2 ^ (prefixWord ++ tailWord_5193729).sum := by decide
  have hdescent : baseEnd_5193729 < baseStart_5193729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193752 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_5193752 : Nat := 118140960795 + 5193752 * 2 ^ 59
def prefixEnd_5193752 : Nat := 4983230072969 + 3 ^ 40 * 5193752 * 2
def baseEnd_5193752 : Nat := 888963725416822885038125

theorem tailTrace_5193752 : CollatzResearch.WordTrace tailWord_5193752 prefixEnd_5193752 888963725416822885038125 := by
  unfold tailWord_5193752
  simp only [CollatzResearch.WordTrace]
  refine ⟨94715848939965500533631755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126287798586620667378175673 94715848939965500533631755)
  ·
    refine ⟨142073773409948250800447633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94715848939965500533631755 142073773409948250800447633)
    ·
      refine ⟨106555330057461188100335725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142073773409948250800447633 106555330057461188100335725)
      ·
        refine ⟨39958248771547945537625897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106555330057461188100335725 39958248771547945537625897)
        ·
          refine ⟨29968686578660959153219423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39958248771547945537625897 29968686578660959153219423)
          ·
            refine ⟨44953029867991438729829135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29968686578660959153219423 44953029867991438729829135)
            ·
              refine ⟨67429544801987158094743703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44953029867991438729829135 67429544801987158094743703)
              ·
                refine ⟨101144317202980737142115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67429544801987158094743703 101144317202980737142115555)
                ·
                  refine ⟨151716475804471105713173333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101144317202980737142115555 151716475804471105713173333)
                  ·
                    refine ⟨888963725416822885038125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151716475804471105713173333 888963725416822885038125)
                    ·
                      rfl

theorem cell23_5193752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_5193752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193752 prefixEnd_5193752 := by exact prefixLift 5193752
  have htrace : WordTrace (prefixWord ++ tailWord_5193752) baseStart_5193752 baseEnd_5193752 := by
    simpa [prefixWord, tailWord_5193752, baseEnd_5193752] using wordTrace_append hprefix tailTrace_5193752
  have hstable : (prefixWord ++ tailWord_5193752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193752).length < 2 ^ (prefixWord ++ tailWord_5193752).sum := by decide
  have hdescent : baseEnd_5193752 < baseStart_5193752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193776 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 3, 3, 2]
def baseStart_5193776 : Nat := 118140960795 + 5193776 * 2 ^ 59
def prefixEnd_5193776 : Nat := 4983230072969 + 3 ^ 40 * 5193776 * 2
def baseEnd_5193776 : Nat := 2666903499786176561214265

theorem tailTrace_5193776 : CollatzResearch.WordTrace tailWord_5193776 prefixEnd_5193776 2666903499786176561214265 := by
  unfold tailWord_5193776
  simp only [CollatzResearch.WordTrace]
  refine ⟨94716286615922026583068591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126288382154562702110758121 94716286615922026583068591)
  ·
    refine ⟨142074429923883039874602887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94716286615922026583068591 142074429923883039874602887)
    ·
      refine ⟨213111644885824559811904331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142074429923883039874602887 213111644885824559811904331)
      ·
        refine ⟨319667467328736839717856497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213111644885824559811904331 319667467328736839717856497)
        ·
          refine ⟨239750600496552629788392373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319667467328736839717856497 239750600496552629788392373)
          ·
            refine ⟨22476618796551809042661785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239750600496552629788392373 22476618796551809042661785)
            ·
              refine ⟨16857464097413856781996339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22476618796551809042661785 16857464097413856781996339)
              ·
                refine ⟨25286196146120785172994509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16857464097413856781996339 25286196146120785172994509)
                ·
                  refine ⟨9482323554795294439872941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25286196146120785172994509 9482323554795294439872941)
                  ·
                    refine ⟨3555871333048235414952353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9482323554795294439872941 3555871333048235414952353)
                    ·
                      refine ⟨2666903499786176561214265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555871333048235414952353 2666903499786176561214265)
                      ·
                        rfl

theorem cell23_5193776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 3, 2].length) (baseStart_5193776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193776 prefixEnd_5193776 := by exact prefixLift 5193776
  have htrace : WordTrace (prefixWord ++ tailWord_5193776) baseStart_5193776 baseEnd_5193776 := by
    simpa [prefixWord, tailWord_5193776, baseEnd_5193776] using wordTrace_append hprefix tailTrace_5193776
  have hstable : (prefixWord ++ tailWord_5193776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193776).length < 2 ^ (prefixWord ++ tailWord_5193776).sum := by decide
  have hdescent : baseEnd_5193776 < baseStart_5193776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193829 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 7]
def baseStart_5193829 : Nat := 118140960795 + 5193829 * 2 ^ 59
def prefixEnd_5193829 : Nat := 4983230072969 + 3 ^ 40 * 5193829 * 2
def baseEnd_5193829 : Nat := 296325634917873872650169

theorem tailTrace_5193829 : CollatzResearch.WordTrace tailWord_5193829 prefixEnd_5193829 296325634917873872650169 := by
  unfold tailWord_5193829
  simp only [CollatzResearch.WordTrace]
  refine ⟨189434506300652043217816541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126289670867101362145211027 189434506300652043217816541)
  ·
    refine ⟨71037939862744516206681203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189434506300652043217816541 71037939862744516206681203)
    ·
      refine ⟨106556909794116774310021805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71037939862744516206681203 106556909794116774310021805)
      ·
        refine ⟨39958841172793790366258177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106556909794116774310021805 39958841172793790366258177)
        ·
          refine ⟨29969130879595342774693633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39958841172793790366258177 29969130879595342774693633)
          ·
            refine ⟨22476848159696507081020225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29969130879595342774693633 22476848159696507081020225)
            ·
              refine ⟨16857636119772380310765169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22476848159696507081020225 16857636119772380310765169)
              ·
                refine ⟨12643227089829285233073877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16857636119772380310765169 12643227089829285233073877)
                ·
                  refine ⟨296325634917873872650169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12643227089829285233073877 296325634917873872650169)
                  ·
                    rfl

theorem cell23_5193829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_5193829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193829 prefixEnd_5193829 := by exact prefixLift 5193829
  have htrace : WordTrace (prefixWord ++ tailWord_5193829) baseStart_5193829 baseEnd_5193829 := by
    simpa [prefixWord, tailWord_5193829, baseEnd_5193829] using wordTrace_append hprefix tailTrace_5193829
  have hstable : (prefixWord ++ tailWord_5193829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193829).length < 2 ^ (prefixWord ++ tailWord_5193829).sum := by decide
  have hdescent : baseEnd_5193829 < baseStart_5193829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193859 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 4, 5]
def baseStart_5193859 : Nat := 118140960795 + 5193859 * 2 ^ 59
def prefixEnd_5193859 : Nat := 4983230072969 + 3 ^ 40 * 5193859 * 2
def baseEnd_5193859 : Nat := 888982039560166578825461

theorem tailTrace_5193859 : CollatzResearch.WordTrace tailWord_5193859 prefixEnd_5193859 888982039560166578825461 := by
  unfold tailWord_5193859
  simp only [CollatzResearch.WordTrace]
  refine ⟨189435600490543358341408631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126290400327028905560939087 189435600490543358341408631)
  ·
    refine ⟨284153400735815037512112947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189435600490543358341408631 284153400735815037512112947)
    ·
      refine ⟨426230101103722556268169421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284153400735815037512112947 426230101103722556268169421)
      ·
        refine ⟨159836287913895958600563533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426230101103722556268169421 159836287913895958600563533)
        ·
          refine ⟨59938607967710984475211325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159836287913895958600563533 59938607967710984475211325)
          ·
            refine ⟨22476977987891619178204247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59938607967710984475211325 22476977987891619178204247)
            ·
              refine ⟨33715466981837428767306371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22476977987891619178204247 33715466981837428767306371)
              ·
                refine ⟨50573200472756143150959557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33715466981837428767306371 50573200472756143150959557)
                ·
                  refine ⟨9482475088641776840804917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50573200472756143150959557 9482475088641776840804917)
                  ·
                    refine ⟨888982039560166578825461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9482475088641776840804917 888982039560166578825461)
                    ·
                      rfl

theorem cell23_5193859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 5].length) (baseStart_5193859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193859 prefixEnd_5193859 := by exact prefixLift 5193859
  have htrace : WordTrace (prefixWord ++ tailWord_5193859) baseStart_5193859 baseEnd_5193859 := by
    simpa [prefixWord, tailWord_5193859, baseEnd_5193859] using wordTrace_append hprefix tailTrace_5193859
  have hstable : (prefixWord ++ tailWord_5193859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193859).length < 2 ^ (prefixWord ++ tailWord_5193859).sum := by decide
  have hdescent : baseEnd_5193859 < baseStart_5193859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193878 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5193878 : Nat := 118140960795 + 5193878 * 2 ^ 59
def prefixEnd_5193878 : Nat := 4983230072969 + 3 ^ 40 * 5193878 * 2
def baseEnd_5193878 : Nat := 2666955874812935162138797

theorem tailTrace_5193878 : CollatzResearch.WordTrace tailWord_5193878 prefixEnd_5193878 2666955874812935162138797 := by
  unfold tailWord_5193878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11839768342342157786646893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126290862318316349724233525 11839768342342157786646893)
  ·
    refine ⟨4439913128378309169992585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11839768342342157786646893 4439913128378309169992585)
    ·
      refine ⟨3329934846283731877494439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4439913128378309169992585 3329934846283731877494439)
      ·
        refine ⟨4994902269425597816241659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329934846283731877494439 4994902269425597816241659)
        ·
          refine ⟨7492353404138396724362489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4994902269425597816241659 7492353404138396724362489)
          ·
            refine ⟨5619265053103797543271867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7492353404138396724362489 5619265053103797543271867)
            ·
              refine ⟨8428897579655696314907801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619265053103797543271867 8428897579655696314907801)
              ·
                refine ⟨6321673184741772236180851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8428897579655696314907801 6321673184741772236180851)
                ·
                  refine ⟨9482509777112658354271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6321673184741772236180851 9482509777112658354271277)
                  ·
                    refine ⟨3555941166417246882851729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9482509777112658354271277 3555941166417246882851729)
                    ·
                      refine ⟨2666955874812935162138797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3555941166417246882851729 2666955874812935162138797)
                      ·
                        rfl

theorem cell23_5193878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5193878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193878 prefixEnd_5193878 := by exact prefixLift 5193878
  have htrace : WordTrace (prefixWord ++ tailWord_5193878) baseStart_5193878 baseEnd_5193878 := by
    simpa [prefixWord, tailWord_5193878, baseEnd_5193878] using wordTrace_append hprefix tailTrace_5193878
  have hstable : (prefixWord ++ tailWord_5193878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193878).length < 2 ^ (prefixWord ++ tailWord_5193878).sum := by decide
  have hdescent : baseEnd_5193878 < baseStart_5193878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193899 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 3]
def baseStart_5193899 : Nat := 118140960795 + 5193899 * 2 ^ 59
def prefixEnd_5193899 : Nat := 4983230072969 + 3 ^ 40 * 5193899 * 2
def baseEnd_5193899 : Nat := 2666966657906679579976199

theorem tailTrace_5193899 : CollatzResearch.WordTrace tailWord_5193899 prefixEnd_5193899 2666966657906679579976199 := by
  unfold tailWord_5193899
  simp only [CollatzResearch.WordTrace]
  refine ⟨189437059410398445172864751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126291372940265630115243167 189437059410398445172864751)
  ·
    refine ⟨284155589115597667759297127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189437059410398445172864751 284155589115597667759297127)
    ·
      refine ⟨426233383673396501638945691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284155589115597667759297127 426233383673396501638945691)
      ·
        refine ⟨639350075510094752458418537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426233383673396501638945691 639350075510094752458418537)
        ·
          refine ⟨479512556632571064343813903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639350075510094752458418537 479512556632571064343813903)
          ·
            refine ⟨719268834948856596515720855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479512556632571064343813903 719268834948856596515720855)
            ·
              refine ⟨1078903252423284894773581283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719268834948856596515720855 1078903252423284894773581283)
              ·
                refine ⟨1618354878634927342160371925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078903252423284894773581283 1618354878634927342160371925)
                ·
                  refine ⟨37930192468006109581883717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1618354878634927342160371925 37930192468006109581883717)
                  ·
                    refine ⟨7111911087751145546603197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37930192468006109581883717 7111911087751145546603197)
                    ·
                      refine ⟨2666966657906679579976199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7111911087751145546603197 2666966657906679579976199)
                      ·
                        rfl

theorem cell23_5193899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 3].length) (baseStart_5193899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193899 prefixEnd_5193899 := by exact prefixLift 5193899
  have htrace : WordTrace (prefixWord ++ tailWord_5193899) baseStart_5193899 baseEnd_5193899 := by
    simpa [prefixWord, tailWord_5193899, baseEnd_5193899] using wordTrace_append hprefix tailTrace_5193899
  have hstable : (prefixWord ++ tailWord_5193899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193899).length < 2 ^ (prefixWord ++ tailWord_5193899).sum := by decide
  have hdescent : baseEnd_5193899 < baseStart_5193899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5193980 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_5193980 : Nat := 118140960795 + 5193980 * 2 ^ 59
def prefixEnd_5193980 : Nat := 4983230072969 + 3 ^ 40 * 5193980 * 2
def baseEnd_5193980 : Nat := 2667008249839693763063327

theorem tailTrace_5193980 : CollatzResearch.WordTrace tailWord_5193980 prefixEnd_5193980 2667008249839693763063327 := by
  unfold tailWord_5193980
  simp only [CollatzResearch.WordTrace]
  refine ⟨94720006861552498003281697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126293342482069997337708929 94720006861552498003281697)
  ·
    refine ⟨71040005146164373502461273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94720006861552498003281697 71040005146164373502461273)
    ·
      refine ⟨53280003859623280126845955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71040005146164373502461273 53280003859623280126845955)
      ·
        refine ⟨79920005789434920190268933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53280003859623280126845955 79920005789434920190268933)
        ·
          refine ⟨14985001085519047535675425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79920005789434920190268933 14985001085519047535675425)
          ·
            refine ⟨11238750814139285651756569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14985001085519047535675425 11238750814139285651756569)
            ·
              refine ⟨8429063110604464238817427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11238750814139285651756569 8429063110604464238817427)
              ·
                refine ⟨12643594665906696358226141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8429063110604464238817427 12643594665906696358226141)
                ·
                  refine ⟨4741347999715011134334803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12643594665906696358226141 4741347999715011134334803)
                  ·
                    refine ⟨7112021999572516701502205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4741347999715011134334803 7112021999572516701502205)
                    ·
                      refine ⟨2667008249839693763063327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7112021999572516701502205 2667008249839693763063327)
                      ·
                        rfl

theorem cell23_5193980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_5193980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5193980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5193980 prefixEnd_5193980 := by exact prefixLift 5193980
  have htrace : WordTrace (prefixWord ++ tailWord_5193980) baseStart_5193980 baseEnd_5193980 := by
    simpa [prefixWord, tailWord_5193980, baseEnd_5193980] using wordTrace_append hprefix tailTrace_5193980
  have hstable : (prefixWord ++ tailWord_5193980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5193980).length < 2 ^ (prefixWord ++ tailWord_5193980).sum := by decide
  have hdescent : baseEnd_5193980 < baseStart_5193980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5193980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194066 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_5194066 : Nat := 118140960795 + 5194066 * 2 ^ 59
def prefixEnd_5194066 : Nat := 4983230072969 + 3 ^ 40 * 5194066 * 2
def baseEnd_5194066 : Nat := 2667052409175980426587931

theorem tailTrace_5194066 : CollatzResearch.WordTrace tailWord_5194066 prefixEnd_5194066 2667052409175980426587931 := by
  unfold tailWord_5194066
  simp only [CollatzResearch.WordTrace]
  refine ⟨47360787600198358173548513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126295433600528955129462701 47360787600198358173548513)
  ·
    refine ⟨35520590700148768630161385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47360787600198358173548513 35520590700148768630161385)
    ·
      refine ⟨26640443025111576472621039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35520590700148768630161385 26640443025111576472621039)
      ·
        refine ⟨39960664537667364708931559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26640443025111576472621039 39960664537667364708931559)
        ·
          refine ⟨59940996806501047063397339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39960664537667364708931559 59940996806501047063397339)
          ·
            refine ⟨89911495209751570595096009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59940996806501047063397339 89911495209751570595096009)
            ·
              refine ⟨67433621407313677946322007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89911495209751570595096009 67433621407313677946322007)
              ·
                refine ⟨101150432110970516919483011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67433621407313677946322007 101150432110970516919483011)
                ·
                  refine ⟨151725648166455775379224517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101150432110970516919483011 151725648166455775379224517)
                  ·
                    refine ⟨28448559031210457883604597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151725648166455775379224517 28448559031210457883604597)
                    ·
                      refine ⟨2667052409175980426587931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28448559031210457883604597 2667052409175980426587931)
                      ·
                        rfl

theorem cell23_5194066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_5194066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194066 prefixEnd_5194066 := by exact prefixLift 5194066
  have htrace : WordTrace (prefixWord ++ tailWord_5194066) baseStart_5194066 baseEnd_5194066 := by
    simpa [prefixWord, tailWord_5194066, baseEnd_5194066] using wordTrace_append hprefix tailTrace_5194066
  have hstable : (prefixWord ++ tailWord_5194066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194066).length < 2 ^ (prefixWord ++ tailWord_5194066).sum := by decide
  have hdescent : baseEnd_5194066 < baseStart_5194066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194087 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_5194087 : Nat := 118140960795 + 5194087 * 2 ^ 59
def prefixEnd_5194087 : Nat := 4983230072969 + 3 ^ 40 * 5194087 * 2
def baseEnd_5194087 : Nat := 2667063192269724844425335

theorem tailTrace_5194087 : CollatzResearch.WordTrace tailWord_5194087 prefixEnd_5194087 2667063192269724844425335 := by
  unfold tailWord_5194087
  simp only [CollatzResearch.WordTrace]
  refine ⟨189443916333717353280708515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126295944222478235520472343 189443916333717353280708515)
  ·
    refine ⟨284165874500576029921062773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189443916333717353280708515 284165874500576029921062773)
    ·
      refine ⟨26640550734429002805099635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284165874500576029921062773 26640550734429002805099635)
      ·
        refine ⟨39960826101643504207649453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26640550734429002805099635 39960826101643504207649453)
        ·
          refine ⟨14985309788116314077868545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39960826101643504207649453 14985309788116314077868545)
          ·
            refine ⟨11238982341087235558401409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14985309788116314077868545 11238982341087235558401409)
            ·
              refine ⟨8429236755815426668801057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11238982341087235558401409 8429236755815426668801057)
              ·
                refine ⟨6321927566861570001600793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8429236755815426668801057 6321927566861570001600793)
                ·
                  refine ⟨4741445675146177501200595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321927566861570001600793 4741445675146177501200595)
                  ·
                    refine ⟨7112168512719266251800893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4741445675146177501200595 7112168512719266251800893)
                    ·
                      refine ⟨2667063192269724844425335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7112168512719266251800893 2667063192269724844425335)
                      ·
                        rfl

theorem cell23_5194087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_5194087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194087 prefixEnd_5194087 := by exact prefixLift 5194087
  have htrace : WordTrace (prefixWord ++ tailWord_5194087) baseStart_5194087 baseEnd_5194087 := by
    simpa [prefixWord, tailWord_5194087, baseEnd_5194087] using wordTrace_append hprefix tailTrace_5194087
  have hstable : (prefixWord ++ tailWord_5194087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194087).length < 2 ^ (prefixWord ++ tailWord_5194087).sum := by decide
  have hdescent : baseEnd_5194087 < baseStart_5194087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194143 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_5194143 : Nat := 118140960795 + 5194143 * 2 ^ 59
def prefixEnd_5194143 : Nat := 4983230072969 + 3 ^ 40 * 5194143 * 2
def baseEnd_5194143 : Nat := 2667091947186376625325077

theorem tailTrace_5194143 : CollatzResearch.WordTrace tailWord_5194143 prefixEnd_5194143 2667091947186376625325077 := by
  unfold tailWord_5194143
  simp only [CollatzResearch.WordTrace]
  refine ⟨189445958821514474844747083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126297305881009649896498055 189445958821514474844747083)
  ·
    refine ⟨284168938232271712267120625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189445958821514474844747083 284168938232271712267120625)
    ·
      refine ⟨213126703674203784200340469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284168938232271712267120625 213126703674203784200340469)
      ·
        refine ⟨19980628469456604768781919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213126703674203784200340469 19980628469456604768781919)
        ·
          refine ⟨29970942704184907153172879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19980628469456604768781919 29970942704184907153172879)
          ·
            refine ⟨44956414056277360729759319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29970942704184907153172879 44956414056277360729759319)
            ·
              refine ⟨67434621084416041094638979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44956414056277360729759319 67434621084416041094638979)
              ·
                refine ⟨101151931626624061641958469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67434621084416041094638979 101151931626624061641958469)
                ·
                  refine ⟨18965987179992011557867213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101151931626624061641958469 18965987179992011557867213)
                  ·
                    refine ⟨7112245192497004334200205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18965987179992011557867213 7112245192497004334200205)
                    ·
                      refine ⟨2667091947186376625325077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7112245192497004334200205 2667091947186376625325077)
                      ·
                        rfl

theorem cell23_5194143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_5194143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194143 prefixEnd_5194143 := by exact prefixLift 5194143
  have htrace : WordTrace (prefixWord ++ tailWord_5194143) baseStart_5194143 baseEnd_5194143 := by
    simpa [prefixWord, tailWord_5194143, baseEnd_5194143] using wordTrace_append hprefix tailTrace_5194143
  have hstable : (prefixWord ++ tailWord_5194143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194143).length < 2 ^ (prefixWord ++ tailWord_5194143).sum := by decide
  have hdescent : baseEnd_5194143 < baseStart_5194143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194144 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 2, 2, 2]
def baseStart_5194144 : Nat := 118140960795 + 5194144 * 2 ^ 59
def prefixEnd_5194144 : Nat := 4983230072969 + 3 ^ 40 * 5194144 * 2
def baseEnd_5194144 : Nat := 2667092460667031121412573

theorem tailTrace_5194144 : CollatzResearch.WordTrace tailWord_5194144 prefixEnd_5194144 2667092460667031121412573 := by
  unfold tailWord_5194144
  simp only [CollatzResearch.WordTrace]
  refine ⟨94722997647255426007766743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126297330196340568010355657 94722997647255426007766743)
  ·
    refine ⟨142084496470883139011650115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94722997647255426007766743 142084496470883139011650115)
    ·
      refine ⟨213126744706324708517475173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142084496470883139011650115 213126744706324708517475173)
      ·
        refine ⟨39961264632435882847026595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213126744706324708517475173 39961264632435882847026595)
        ·
          refine ⟨59941896948653824270539893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39961264632435882847026595 59941896948653824270539893)
          ·
            refine ⟨5619552838936296025363115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59941896948653824270539893 5619552838936296025363115)
            ·
              refine ⟨8429329258404444038044673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619552838936296025363115 8429329258404444038044673)
              ·
                refine ⟨6321996943803333028533505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8429329258404444038044673 6321996943803333028533505)
                ·
                  refine ⟨4741497707852499771400129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321996943803333028533505 4741497707852499771400129)
                  ·
                    refine ⟨3556123280889374828550097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4741497707852499771400129 3556123280889374828550097)
                    ·
                      refine ⟨2667092460667031121412573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556123280889374828550097 2667092460667031121412573)
                      ·
                        rfl

theorem cell23_5194144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_5194144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194144 prefixEnd_5194144 := by exact prefixLift 5194144
  have htrace : WordTrace (prefixWord ++ tailWord_5194144) baseStart_5194144 baseEnd_5194144 := by
    simpa [prefixWord, tailWord_5194144, baseEnd_5194144] using wordTrace_append hprefix tailTrace_5194144
  have hstable : (prefixWord ++ tailWord_5194144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194144).length < 2 ^ (prefixWord ++ tailWord_5194144).sum := by decide
  have hdescent : baseEnd_5194144 < baseStart_5194144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194153 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 7, 2]
def baseStart_5194153 : Nat := 118140960795 + 5194153 * 2 ^ 59
def prefixEnd_5194153 : Nat := 4983230072969 + 3 ^ 40 * 5194153 * 2
def baseEnd_5194153 : Nat := 2667097081992921586200031

theorem tailTrace_5194153 : CollatzResearch.WordTrace tailWord_5194153 prefixEnd_5194153 2667097081992921586200031 := by
  unfold tailWord_5194153
  simp only [CollatzResearch.WordTrace]
  refine ⟨189446323551478246552611113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126297549034318831035074075 189446323551478246552611113)
  ·
    refine ⟨142084742663608684914458335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189446323551478246552611113 142084742663608684914458335)
    ·
      refine ⟨213127113995413027371687503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142084742663608684914458335 213127113995413027371687503)
      ·
        refine ⟨319690670993119541057531255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213127113995413027371687503 319690670993119541057531255)
        ·
          refine ⟨479536006489679311586296883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319690670993119541057531255 479536006489679311586296883)
          ·
            refine ⟨719304009734518967379445325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479536006489679311586296883 719304009734518967379445325)
            ·
              refine ⟨269739003650444612767291997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 719304009734518967379445325 269739003650444612767291997)
              ·
                refine ⟨101152126368916729787734499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269739003650444612767291997 101152126368916729787734499)
                ·
                  refine ⟨151728189553375094681601749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101152126368916729787734499 151728189553375094681601749)
                  ·
                    refine ⟨3556129442657228781600041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151728189553375094681601749 3556129442657228781600041)
                    ·
                      refine ⟨2667097081992921586200031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556129442657228781600041 2667097081992921586200031)
                      ·
                        rfl

theorem cell23_5194153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 7, 2].length) (baseStart_5194153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194153 prefixEnd_5194153 := by exact prefixLift 5194153
  have htrace : WordTrace (prefixWord ++ tailWord_5194153) baseStart_5194153 baseEnd_5194153 := by
    simpa [prefixWord, tailWord_5194153, baseEnd_5194153] using wordTrace_append hprefix tailTrace_5194153
  have hstable : (prefixWord ++ tailWord_5194153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194153).length < 2 ^ (prefixWord ++ tailWord_5194153).sum := by decide
  have hdescent : baseEnd_5194153 < baseStart_5194153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194156 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_5194156 : Nat := 118140960795 + 5194156 * 2 ^ 59
def prefixEnd_5194156 : Nat := 4983230072969 + 3 ^ 40 * 5194156 * 2
def baseEnd_5194156 : Nat := 2667098622434885074462517

theorem tailTrace_5194156 : CollatzResearch.WordTrace tailWord_5194156 prefixEnd_5194156 2667098622434885074462517 := by
  unfold tailWord_5194156
  simp only [CollatzResearch.WordTrace]
  refine ⟨94723216485233689032485161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126297621980311585376646881 94723216485233689032485161)
  ·
    refine ⟨71042412363925266774363871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94723216485233689032485161 71042412363925266774363871)
    ·
      refine ⟨106563618545887900161545807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71042412363925266774363871 106563618545887900161545807)
      ·
        refine ⟨159845427818831850242318711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106563618545887900161545807 159845427818831850242318711)
        ·
          refine ⟨239768141728247775363478067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159845427818831850242318711 239768141728247775363478067)
          ·
            refine ⟨359652212592371663045217101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239768141728247775363478067 359652212592371663045217101)
            ·
              refine ⟨134869579722139373641956413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359652212592371663045217101 134869579722139373641956413)
              ·
                refine ⟨50576092395802265115733655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134869579722139373641956413 50576092395802265115733655)
                ·
                  refine ⟨75864138593703397673600483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50576092395802265115733655 75864138593703397673600483)
                  ·
                    refine ⟨113796207890555096510400725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75864138593703397673600483 113796207890555096510400725)
                    ·
                      refine ⟨2667098622434885074462517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113796207890555096510400725 2667098622434885074462517)
                      ·
                        rfl

theorem cell23_5194156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_5194156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194156 prefixEnd_5194156 := by exact prefixLift 5194156
  have htrace : WordTrace (prefixWord ++ tailWord_5194156) baseStart_5194156 baseEnd_5194156 := by
    simpa [prefixWord, tailWord_5194156, baseEnd_5194156] using wordTrace_append hprefix tailTrace_5194156
  have hstable : (prefixWord ++ tailWord_5194156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194156).length < 2 ^ (prefixWord ++ tailWord_5194156).sum := by decide
  have hdescent : baseEnd_5194156 < baseStart_5194156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194176 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_5194176 : Nat := 118140960795 + 5194176 * 2 ^ 59
def prefixEnd_5194176 : Nat := 4983230072969 + 3 ^ 40 * 5194176 * 2
def baseEnd_5194176 : Nat := 889036297349324998737475

theorem tailTrace_5194176 : CollatzResearch.WordTrace tailWord_5194176 prefixEnd_5194176 889036297349324998737475 := by
  unfold tailWord_5194176
  simp only [CollatzResearch.WordTrace]
  refine ⟨94723581215197460740349191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126298108286929947653798921 94723581215197460740349191)
  ·
    refine ⟨142085371822796191110523787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94723581215197460740349191 142085371822796191110523787)
    ·
      refine ⟨213128057734194286665785681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142085371822796191110523787 213128057734194286665785681)
      ·
        refine ⟨159846043300645714999339261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213128057734194286665785681 159846043300645714999339261)
        ·
          refine ⟨59942266237742143124752223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159846043300645714999339261 59942266237742143124752223)
          ·
            refine ⟨89913399356613214687128335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59942266237742143124752223 89913399356613214687128335)
            ·
              refine ⟨134870099034919822030692503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89913399356613214687128335 134870099034919822030692503)
              ·
                refine ⟨202305148552379733046038755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134870099034919822030692503 202305148552379733046038755)
                ·
                  refine ⟨303457722828569599569058133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202305148552379733046038755 303457722828569599569058133)
                  ·
                    refine ⟨889036297349324998737475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 303457722828569599569058133 889036297349324998737475)
                    ·
                      rfl

theorem cell23_5194176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_5194176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194176 prefixEnd_5194176 := by exact prefixLift 5194176
  have htrace : WordTrace (prefixWord ++ tailWord_5194176) baseStart_5194176 baseEnd_5194176 := by
    simpa [prefixWord, tailWord_5194176, baseEnd_5194176] using wordTrace_append hprefix tailTrace_5194176
  have hstable : (prefixWord ++ tailWord_5194176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194176).length < 2 ^ (prefixWord ++ tailWord_5194176).sum := by decide
  have hdescent : baseEnd_5194176 < baseStart_5194176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194183 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_5194183 : Nat := 118140960795 + 5194183 * 2 ^ 59
def prefixEnd_5194183 : Nat := 4983230072969 + 3 ^ 40 * 5194183 * 2
def baseEnd_5194183 : Nat := 2667112486412556468824893

theorem tailTrace_5194183 : CollatzResearch.WordTrace tailWord_5194183 prefixEnd_5194183 2667112486412556468824893 := by
  unfold tailWord_5194183
  simp only [CollatzResearch.WordTrace]
  refine ⟨189447417741369561676203203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126298278494246374450802135 189447417741369561676203203)
  ·
    refine ⟨284171126612054342514304805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189447417741369561676203203 284171126612054342514304805)
    ·
      refine ⟨53282086239760189221432151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284171126612054342514304805 53282086239760189221432151)
      ·
        refine ⟨79923129359640283832148227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53282086239760189221432151 79923129359640283832148227)
        ·
          refine ⟨119884694039460425748222341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79923129359640283832148227 119884694039460425748222341)
          ·
            refine ⟨22478380132398829827791689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119884694039460425748222341 22478380132398829827791689)
            ·
              refine ⟨16858785099299122370843767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22478380132398829827791689 16858785099299122370843767)
              ·
                refine ⟨25288177648948683556265651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16858785099299122370843767 25288177648948683556265651)
                ·
                  refine ⟨37932266473423025334398477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25288177648948683556265651 37932266473423025334398477)
                  ·
                    refine ⟨14224599927533634500399429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37932266473423025334398477 14224599927533634500399429)
                    ·
                      refine ⟨2667112486412556468824893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14224599927533634500399429 2667112486412556468824893)
                      ·
                        rfl

theorem cell23_5194183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_5194183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194183 prefixEnd_5194183 := by exact prefixLift 5194183
  have htrace : WordTrace (prefixWord ++ tailWord_5194183) baseStart_5194183 baseEnd_5194183 := by
    simpa [prefixWord, tailWord_5194183, baseEnd_5194183] using wordTrace_append hprefix tailTrace_5194183
  have hstable : (prefixWord ++ tailWord_5194183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194183).length < 2 ^ (prefixWord ++ tailWord_5194183).sum := by decide
  have hdescent : baseEnd_5194183 < baseStart_5194183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194193 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 5, 4]
def baseStart_5194193 : Nat := 118140960795 + 5194193 * 2 ^ 59
def prefixEnd_5194193 : Nat := 4983230072969 + 3 ^ 40 * 5194193 * 2
def baseEnd_5194193 : Nat := 889039207073033809899949

theorem tailTrace_5194193 : CollatzResearch.WordTrace tailWord_5194193 prefixEnd_5194193 889039207073033809899949 := by
  unfold tailWord_5194193
  simp only [CollatzResearch.WordTrace]
  refine ⟨189447782471333333384067233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126298521647555555589378155 189447782471333333384067233)
  ·
    refine ⟨142085836853500000038050425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189447782471333333384067233 142085836853500000038050425)
    ·
      refine ⟨106564377640125000028537819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142085836853500000038050425 106564377640125000028537819)
      ·
        refine ⟨159846566460187500042806729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106564377640125000028537819 159846566460187500042806729)
        ·
          refine ⟨119884924845140625032105047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159846566460187500042806729 119884924845140625032105047)
          ·
            refine ⟨179827387267710937548157571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119884924845140625032105047 179827387267710937548157571)
            ·
              refine ⟨269741080901566406322236357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179827387267710937548157571 269741080901566406322236357)
              ·
                refine ⟨50576452669043701185419317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269741080901566406322236357 50576452669043701185419317)
                ·
                  refine ⟨4741542437722846986133061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50576452669043701185419317 4741542437722846986133061)
                  ·
                    refine ⟨889039207073033809899949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741542437722846986133061 889039207073033809899949)
                    ·
                      rfl

theorem cell23_5194193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_5194193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194193 prefixEnd_5194193 := by exact prefixLift 5194193
  have htrace : WordTrace (prefixWord ++ tailWord_5194193) baseStart_5194193 baseEnd_5194193 := by
    simpa [prefixWord, tailWord_5194193, baseEnd_5194193] using wordTrace_append hprefix tailTrace_5194193
  have hstable : (prefixWord ++ tailWord_5194193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194193).length < 2 ^ (prefixWord ++ tailWord_5194193).sum := by decide
  have hdescent : baseEnd_5194193 < baseStart_5194193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194233 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_5194233 : Nat := 118140960795 + 5194233 * 2 ^ 59
def prefixEnd_5194233 : Nat := 4983230072969 + 3 ^ 40 * 5194233 * 2
def baseEnd_5194233 : Nat := 2667138160445281273199663

theorem tailTrace_5194233 : CollatzResearch.WordTrace tailWord_5194233 prefixEnd_5194233 2667138160445281273199663 := by
  unfold tailWord_5194233
  simp only [CollatzResearch.WordTrace]
  refine ⟨189449241391188420215523353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126299494260792280143682235 189449241391188420215523353)
  ·
    refine ⟨142086931043391315161642515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189449241391188420215523353 142086931043391315161642515)
    ·
      refine ⟨213130396565086972742463773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142086931043391315161642515 213130396565086972742463773)
      ·
        refine ⟨79923898711907614778423915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213130396565086972742463773 79923898711907614778423915)
        ·
          refine ⟨119885848067861422167635873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79923898711907614778423915 119885848067861422167635873)
          ·
            refine ⟨89914386050896066625726905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119885848067861422167635873 89914386050896066625726905)
            ·
              refine ⟨67435789538172049969295179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89914386050896066625726905 67435789538172049969295179)
              ·
                refine ⟨101153684307258074953942769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67435789538172049969295179 101153684307258074953942769)
                ·
                  refine ⟨75865263230443556215457077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101153684307258074953942769 75865263230443556215457077)
                  ·
                    refine ⟨7112368427854083395199101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75865263230443556215457077 7112368427854083395199101)
                    ·
                      refine ⟨2667138160445281273199663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7112368427854083395199101 2667138160445281273199663)
                      ·
                        rfl

theorem cell23_5194233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_5194233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194233 prefixEnd_5194233 := by exact prefixLift 5194233
  have htrace : WordTrace (prefixWord ++ tailWord_5194233) baseStart_5194233 baseEnd_5194233 := by
    simpa [prefixWord, tailWord_5194233, baseEnd_5194233] using wordTrace_append hprefix tailTrace_5194233
  have hstable : (prefixWord ++ tailWord_5194233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194233).length < 2 ^ (prefixWord ++ tailWord_5194233).sum := by decide
  have hdescent : baseEnd_5194233 < baseStart_5194233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194290 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_5194290 : Nat := 118140960795 + 5194290 * 2 ^ 59
def prefixEnd_5194290 : Nat := 4983230072969 + 3 ^ 40 * 5194290 * 2
def baseEnd_5194290 : Nat := 2667167428842587550186901

theorem tailTrace_5194290 : CollatzResearch.WordTrace tailWord_5194290 prefixEnd_5194290 2667167428842587550186901 := by
  unfold tailWord_5194290
  simp only [CollatzResearch.WordTrace]
  refine ⟨47362830087995479737587081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126300880234654612633565549 47362830087995479737587081)
  ·
    refine ⟨35522122565996609803190311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47362830087995479737587081 35522122565996609803190311)
    ·
      refine ⟨53283183848994914704785467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35522122565996609803190311 53283183848994914704785467)
      ·
        refine ⟨79924775773492372057178201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53283183848994914704785467 79924775773492372057178201)
        ·
          refine ⟨59943581830119279042883651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79924775773492372057178201 59943581830119279042883651)
          ·
            refine ⟨89915372745178918564325477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59943581830119279042883651 89915372745178918564325477)
            ·
              refine ⟨16859132389721047230811027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89915372745178918564325477 16859132389721047230811027)
              ·
                refine ⟨25288698584581570846216541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16859132389721047230811027 25288698584581570846216541)
                ·
                  refine ⟨9483261969218089067331203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25288698584581570846216541 9483261969218089067331203)
                  ·
                    refine ⟨14224892953827133600996805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9483261969218089067331203 14224892953827133600996805)
                    ·
                      refine ⟨2667167428842587550186901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14224892953827133600996805 2667167428842587550186901)
                      ·
                        rfl

theorem cell23_5194290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_5194290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194290 prefixEnd_5194290 := by exact prefixLift 5194290
  have htrace : WordTrace (prefixWord ++ tailWord_5194290) baseStart_5194290 baseEnd_5194290 := by
    simpa [prefixWord, tailWord_5194290, baseEnd_5194290] using wordTrace_append hprefix tailTrace_5194290
  have hstable : (prefixWord ++ tailWord_5194290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194290).length < 2 ^ (prefixWord ++ tailWord_5194290).sum := by decide
  have hdescent : baseEnd_5194290 < baseStart_5194290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194294 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_5194294 : Nat := 118140960795 + 5194294 * 2 ^ 59
def prefixEnd_5194294 : Nat := 4983230072969 + 3 ^ 40 * 5194294 * 2
def baseEnd_5194294 : Nat := 2667169482765205534536883

theorem tailTrace_5194294 : CollatzResearch.WordTrace tailWord_5194294 prefixEnd_5194294 2667169482765205534536883 := by
  unfold tailWord_5194294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11840716640247964227093371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126300977495978285088995957 11840716640247964227093371)
  ·
    refine ⟨17761074960371946340640057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11840716640247964227093371 17761074960371946340640057)
    ·
      refine ⟨13320806220278959755480043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17761074960371946340640057 13320806220278959755480043)
      ·
        refine ⟨19981209330418439633220065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13320806220278959755480043 19981209330418439633220065)
        ·
          refine ⟨14985906997813829724915049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19981209330418439633220065 14985906997813829724915049)
          ·
            refine ⟨11239430248360372293686287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14985906997813829724915049 11239430248360372293686287)
            ·
              refine ⟨16859145372540558440529431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11239430248360372293686287 16859145372540558440529431)
              ·
                refine ⟨25288718058810837660794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16859145372540558440529431 25288718058810837660794147)
                ·
                  refine ⟨37933077088216256491191221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25288718058810837660794147 37933077088216256491191221)
                  ·
                    refine ⟨3556225977020274046049177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37933077088216256491191221 3556225977020274046049177)
                    ·
                      refine ⟨2667169482765205534536883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556225977020274046049177 2667169482765205534536883)
                      ·
                        rfl

theorem cell23_5194294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_5194294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194294 prefixEnd_5194294 := by exact prefixLift 5194294
  have htrace : WordTrace (prefixWord ++ tailWord_5194294) baseStart_5194294 baseEnd_5194294 := by
    simpa [prefixWord, tailWord_5194294, baseEnd_5194294] using wordTrace_append hprefix tailTrace_5194294
  have hstable : (prefixWord ++ tailWord_5194294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194294).length < 2 ^ (prefixWord ++ tailWord_5194294).sum := by decide
  have hdescent : baseEnd_5194294 < baseStart_5194294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194300 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_5194300 : Nat := 118140960795 + 5194300 * 2 ^ 59
def prefixEnd_5194300 : Nat := 4983230072969 + 3 ^ 40 * 5194300 * 2
def baseEnd_5194300 : Nat := 889057521216377503687285

theorem tailTrace_5194300 : CollatzResearch.WordTrace tailWord_5194300 prefixEnd_5194300 889057521216377503687285 := by
  unfold tailWord_5194300
  simp only [CollatzResearch.WordTrace]
  refine ⟨94725842540972845329106177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126301123387963793772141569 94725842540972845329106177)
  ·
    refine ⟨71044381905729633996829633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94725842540972845329106177 71044381905729633996829633)
    ·
      refine ⟨53283286429297225497622225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71044381905729633996829633 53283286429297225497622225)
      ·
        refine ⟨39962464821972919123216669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53283286429297225497622225 39962464821972919123216669)
        ·
          refine ⟨14985924308239844671206251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39962464821972919123216669 14985924308239844671206251)
          ·
            refine ⟨22478886462359767006809377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14985924308239844671206251 22478886462359767006809377)
            ·
              refine ⟨16859164846769825255107033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22478886462359767006809377 16859164846769825255107033)
              ·
                refine ⟨12644373635077368941330275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16859164846769825255107033 12644373635077368941330275)
                ·
                  refine ⟨18966560452616053411995413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12644373635077368941330275 18966560452616053411995413)
                  ·
                    refine ⟨889057521216377503687285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18966560452616053411995413 889057521216377503687285)
                    ·
                      rfl

theorem cell23_5194300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_5194300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194300 prefixEnd_5194300 := by exact prefixLift 5194300
  have htrace : WordTrace (prefixWord ++ tailWord_5194300) baseStart_5194300 baseEnd_5194300 := by
    simpa [prefixWord, tailWord_5194300, baseEnd_5194300] using wordTrace_append hprefix tailTrace_5194300
  have hstable : (prefixWord ++ tailWord_5194300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194300).length < 2 ^ (prefixWord ++ tailWord_5194300).sum := by decide
  have hdescent : baseEnd_5194300 < baseStart_5194300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194301 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_5194301 : Nat := 118140960795 + 5194301 * 2 ^ 59
def prefixEnd_5194301 : Nat := 4983230072969 + 3 ^ 40 * 5194301 * 2
def baseEnd_5194301 : Nat := 2667173077129787007149351

theorem tailTrace_5194301 : CollatzResearch.WordTrace tailWord_5194301 prefixEnd_5194301 2667173077129787007149351 := by
  unfold tailWord_5194301
  simp only [CollatzResearch.WordTrace]
  refine ⟨189451721554942067828998757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126301147703294711885999171 189451721554942067828998757)
  ·
    refine ⟨35522197791551637717937267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189451721554942067828998757 35522197791551637717937267)
    ·
      refine ⟨53283296687327456576905901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35522197791551637717937267 53283296687327456576905901)
      ·
        refine ⟨19981236257747796216339713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53283296687327456576905901 19981236257747796216339713)
        ·
          refine ⟨14985927193310847162254785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19981236257747796216339713 14985927193310847162254785)
          ·
            refine ⟨11239445394983135371691089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14985927193310847162254785 11239445394983135371691089)
            ·
              refine ⟨8429584046237351528768317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11239445394983135371691089 8429584046237351528768317)
              ·
                refine ⟨3161094017339006823288119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8429584046237351528768317 3161094017339006823288119)
                ·
                  refine ⟨4741641026008510234932179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161094017339006823288119 4741641026008510234932179)
                  ·
                    refine ⟨7112461539012765352398269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4741641026008510234932179 7112461539012765352398269)
                    ·
                      refine ⟨2667173077129787007149351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7112461539012765352398269 2667173077129787007149351)
                      ·
                        rfl

theorem cell23_5194301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_5194301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194301 prefixEnd_5194301 := by exact prefixLift 5194301
  have htrace : WordTrace (prefixWord ++ tailWord_5194301) baseStart_5194301 baseEnd_5194301 := by
    simpa [prefixWord, tailWord_5194301, baseEnd_5194301] using wordTrace_append hprefix tailTrace_5194301
  have hstable : (prefixWord ++ tailWord_5194301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194301).length < 2 ^ (prefixWord ++ tailWord_5194301).sum := by decide
  have hdescent : baseEnd_5194301 < baseStart_5194301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194308 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 6]
def baseStart_5194308 : Nat := 118140960795 + 5194308 * 2 ^ 59
def prefixEnd_5194308 : Nat := 4983230072969 + 3 ^ 40 * 5194308 * 2
def baseEnd_5194308 : Nat := 296352963499374275529091

theorem tailTrace_5194308 : CollatzResearch.WordTrace tailWord_5194308 prefixEnd_5194308 296352963499374275529091 := by
  unfold tailWord_5194308
  simp only [CollatzResearch.WordTrace]
  refine ⟨94725988432958354012251789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126301317910611138683002385 94725988432958354012251789)
  ·
    refine ⟨35522245662359382754594421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94725988432958354012251789 35522245662359382754594421)
    ·
      refine ⟨3330210530846192133243227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35522245662359382754594421 3330210530846192133243227)
      ·
        refine ⟨4995315796269288199864841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330210530846192133243227 4995315796269288199864841)
        ·
          refine ⟨3746486847201966149898631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4995315796269288199864841 3746486847201966149898631)
          ·
            refine ⟨5619730270802949224847947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746486847201966149898631 5619730270802949224847947)
            ·
              refine ⟨8429595406204423837271921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619730270802949224847947 8429595406204423837271921)
              ·
                refine ⟨6322196554653317877953941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8429595406204423837271921 6322196554653317877953941)
                ·
                  refine ⟨296352963499374275529091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6322196554653317877953941 296352963499374275529091)
                  ·
                    rfl

theorem cell23_5194308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_5194308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194308 prefixEnd_5194308 := by exact prefixLift 5194308
  have htrace : WordTrace (prefixWord ++ tailWord_5194308) baseStart_5194308 baseEnd_5194308 := by
    simpa [prefixWord, tailWord_5194308, baseEnd_5194308] using wordTrace_append hprefix tailTrace_5194308
  have hstable : (prefixWord ++ tailWord_5194308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194308).length < 2 ^ (prefixWord ++ tailWord_5194308).sum := by decide
  have hdescent : baseEnd_5194308 < baseStart_5194308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194324 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_5194324 : Nat := 118140960795 + 5194324 * 2 ^ 59
def prefixEnd_5194324 : Nat := 4983230072969 + 3 ^ 40 * 5194324 * 2
def baseEnd_5194324 : Nat := 2667184887184840417161745

theorem tailTrace_5194324 : CollatzResearch.WordTrace tailWord_5194324 prefixEnd_5194324 2667184887184840417161745 := by
  unfold tailWord_5194324
  simp only [CollatzResearch.WordTrace]
  refine ⟨94726280216929371378543013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126301706955905828504724017 94726280216929371378543013)
  ·
    refine ⟨17761177540674257133476815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94726280216929371378543013 17761177540674257133476815)
    ·
      refine ⟨26641766311011385700215223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17761177540674257133476815 26641766311011385700215223)
      ·
        refine ⟨39962649466517078550322835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26641766311011385700215223 39962649466517078550322835)
        ·
          refine ⟨59943974199775617825484253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39962649466517078550322835 59943974199775617825484253)
          ·
            refine ⟨22478990324915856684556595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59943974199775617825484253 22478990324915856684556595)
            ·
              refine ⟨33718485487373785026834893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22478990324915856684556595 33718485487373785026834893)
              ·
                refine ⟨12644432057765169385063085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33718485487373785026834893 12644432057765169385063085)
                ·
                  refine ⟨4741662021661938519398657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12644432057765169385063085 4741662021661938519398657)
                  ·
                    refine ⟨3556246516246453889548993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4741662021661938519398657 3556246516246453889548993)
                    ·
                      refine ⟨2667184887184840417161745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556246516246453889548993 2667184887184840417161745)
                      ·
                        rfl

theorem cell23_5194324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_5194324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194324 prefixEnd_5194324 := by exact prefixLift 5194324
  have htrace : WordTrace (prefixWord ++ tailWord_5194324) baseStart_5194324 baseEnd_5194324 := by
    simpa [prefixWord, tailWord_5194324, baseEnd_5194324] using wordTrace_append hprefix tailTrace_5194324
  have hstable : (prefixWord ++ tailWord_5194324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194324).length < 2 ^ (prefixWord ++ tailWord_5194324).sum := by decide
  have hdescent : baseEnd_5194324 < baseStart_5194324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194337 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_5194337 : Nat := 118140960795 + 5194337 * 2 ^ 59
def prefixEnd_5194337 : Nat := 4983230072969 + 3 ^ 40 * 5194337 * 2
def baseEnd_5194337 : Nat := 2667191562433348866299185

theorem tailTrace_5194337 : CollatzResearch.WordTrace tailWord_5194337 prefixEnd_5194337 2667191562433348866299185 := by
  unfold tailWord_5194337
  simp only [CollatzResearch.WordTrace]
  refine ⟨189453034582811645977309265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126302023055207763984872843 189453034582811645977309265)
  ·
    refine ⟨142089775937108734482981949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189453034582811645977309265 142089775937108734482981949)
    ·
      refine ⟨53283665976415775431118231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142089775937108734482981949 53283665976415775431118231)
      ·
        refine ⟨79925498964623663146677347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53283665976415775431118231 79925498964623663146677347)
        ·
          refine ⟨119888248446935494720016021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79925498964623663146677347 119888248446935494720016021)
          ·
            refine ⟨5619761645950101315000751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119888248446935494720016021 5619761645950101315000751)
            ·
              refine ⟨8429642468925151972501127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619761645950101315000751 8429642468925151972501127)
              ·
                refine ⟨12644463703387727958751691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8429642468925151972501127 12644463703387727958751691)
                ·
                  refine ⟨18966695555081591938127537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12644463703387727958751691 18966695555081591938127537)
                  ·
                    refine ⟨14225021666311193953595653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18966695555081591938127537 14225021666311193953595653)
                    ·
                      refine ⟨2667191562433348866299185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14225021666311193953595653 2667191562433348866299185)
                      ·
                        rfl

theorem cell23_5194337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_5194337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194337 prefixEnd_5194337 := by exact prefixLift 5194337
  have htrace : WordTrace (prefixWord ++ tailWord_5194337) baseStart_5194337 baseEnd_5194337 := by
    simpa [prefixWord, tailWord_5194337, baseEnd_5194337] using wordTrace_append hprefix tailTrace_5194337
  have hstable : (prefixWord ++ tailWord_5194337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194337).length < 2 ^ (prefixWord ++ tailWord_5194337).sum := by decide
  have hdescent : baseEnd_5194337 < baseStart_5194337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194431 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 2, 2, 2]
def baseStart_5194431 : Nat := 118140960795 + 5194431 * 2 ^ 59
def prefixEnd_5194431 : Nat := 4983230072969 + 3 ^ 40 * 5194431 * 2
def baseEnd_5194431 : Nat := 2667239829614871498523753

theorem tailTrace_5194431 : CollatzResearch.WordTrace tailWord_5194431 prefixEnd_5194431 2667239829614871498523753 := by
  unfold tailWord_5194431
  simp only [CollatzResearch.WordTrace]
  refine ⟨189456463044471100031231147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126304308696314066687487431 189456463044471100031231147)
  ·
    refine ⟨284184694566706650046846721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189456463044471100031231147 284184694566706650046846721)
    ·
      refine ⟨213138520925029987535135041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284184694566706650046846721 213138520925029987535135041)
      ·
        refine ⟨159853890693772490651351281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213138520925029987535135041 159853890693772490651351281)
        ·
          refine ⟨119890418020329367988513461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159853890693772490651351281 119890418020329367988513461)
          ·
            refine ⟨11239726689405878248923137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119890418020329367988513461 11239726689405878248923137)
            ·
              refine ⟨8429795017054408686692353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11239726689405878248923137 8429795017054408686692353)
              ·
                refine ⟨6322346262790806515019265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8429795017054408686692353 6322346262790806515019265)
                ·
                  refine ⟨4741759697093104886264449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6322346262790806515019265 4741759697093104886264449)
                  ·
                    refine ⟨3556319772819828664698337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4741759697093104886264449 3556319772819828664698337)
                    ·
                      refine ⟨2667239829614871498523753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556319772819828664698337 2667239829614871498523753)
                      ·
                        rfl

theorem cell23_5194431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_5194431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194431 prefixEnd_5194431 := by exact prefixLift 5194431
  have htrace : WordTrace (prefixWord ++ tailWord_5194431) baseStart_5194431 baseEnd_5194431 := by
    simpa [prefixWord, tailWord_5194431, baseEnd_5194431] using wordTrace_append hprefix tailTrace_5194431
  have hstable : (prefixWord ++ tailWord_5194431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194431).length < 2 ^ (prefixWord ++ tailWord_5194431).sum := by decide
  have hdescent : baseEnd_5194431 < baseStart_5194431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194457 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 2, 5, 2]
def baseStart_5194457 : Nat := 118140960795 + 5194457 * 2 ^ 59
def prefixEnd_5194457 : Nat := 4983230072969 + 3 ^ 40 * 5194457 * 2
def baseEnd_5194457 : Nat := 2667253180111888396798633

theorem tailTrace_5194457 : CollatzResearch.WordTrace tailWord_5194457 prefixEnd_5194457 2667253180111888396798633 := by
  unfold tailWord_5194457
  simp only [CollatzResearch.WordTrace]
  refine ⟨189457411342376906471677625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126304940894917937647785083 189457411342376906471677625)
  ·
    refine ⟨142093058506782679853758219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189457411342376906471677625 142093058506782679853758219)
    ·
      refine ⟨213139587760174019780637329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142093058506782679853758219 213139587760174019780637329)
      ·
        refine ⟨159854690820130514835477997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213139587760174019780637329 159854690820130514835477997)
        ·
          refine ⟨59945509057548943063304249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159854690820130514835477997 59945509057548943063304249)
          ·
            refine ⟨44959131793161707297478187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59945509057548943063304249 44959131793161707297478187)
            ·
              refine ⟨67438697689742560946217281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44959131793161707297478187 67438697689742560946217281)
              ·
                refine ⟨50579023267306920709662961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67438697689742560946217281 50579023267306920709662961)
                ·
                  refine ⟨37934267450480190532247221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50579023267306920709662961 37934267450480190532247221)
                  ·
                    refine ⟨3556337573482517862398177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37934267450480190532247221 3556337573482517862398177)
                    ·
                      refine ⟨2667253180111888396798633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556337573482517862398177 2667253180111888396798633)
                      ·
                        rfl

theorem cell23_5194457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_5194457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194457 prefixEnd_5194457 := by exact prefixLift 5194457
  have htrace : WordTrace (prefixWord ++ tailWord_5194457) baseStart_5194457 baseEnd_5194457 := by
    simpa [prefixWord, tailWord_5194457, baseEnd_5194457] using wordTrace_append hprefix tailTrace_5194457
  have hstable : (prefixWord ++ tailWord_5194457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194457).length < 2 ^ (prefixWord ++ tailWord_5194457).sum := by decide
  have hdescent : baseEnd_5194457 < baseStart_5194457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194467 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 1, 7]
def baseStart_5194467 : Nat := 118140960795 + 5194467 * 2 ^ 59
def prefixEnd_5194467 : Nat := 4983230072969 + 3 ^ 40 * 5194467 * 2
def baseEnd_5194467 : Nat := 889086104972811119224529

theorem tailTrace_5194467 : CollatzResearch.WordTrace tailWord_5194467 prefixEnd_5194467 889086104972811119224529 := by
  unfold tailWord_5194467
  simp only [CollatzResearch.WordTrace]
  refine ⟨189457776072340678179541655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126305184048227118786361103 189457776072340678179541655)
  ·
    refine ⟨284186664108511017269312483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189457776072340678179541655 284186664108511017269312483)
    ·
      refine ⟨426279996162766525903968725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284186664108511017269312483 426279996162766525903968725)
      ·
        refine ⟨9990937410064840450874267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 426279996162766525903968725 9990937410064840450874267)
        ·
          refine ⟨14986406115097260676311401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990937410064840450874267 14986406115097260676311401)
          ·
            refine ⟨11239804586322945507233551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14986406115097260676311401 11239804586322945507233551)
            ·
              refine ⟨16859706879484418260850327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11239804586322945507233551 16859706879484418260850327)
              ·
                refine ⟨25289560319226627391275491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16859706879484418260850327 25289560319226627391275491)
                ·
                  refine ⟨37934340478839941086913237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25289560319226627391275491 37934340478839941086913237)
                  ·
                    refine ⟨889086104972811119224529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37934340478839941086913237 889086104972811119224529)
                    ·
                      rfl

theorem cell23_5194467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 7].length) (baseStart_5194467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194467 prefixEnd_5194467 := by exact prefixLift 5194467
  have htrace : WordTrace (prefixWord ++ tailWord_5194467) baseStart_5194467 baseEnd_5194467 := by
    simpa [prefixWord, tailWord_5194467, baseEnd_5194467] using wordTrace_append hprefix tailTrace_5194467
  have hstable : (prefixWord ++ tailWord_5194467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194467).length < 2 ^ (prefixWord ++ tailWord_5194467).sum := by decide
  have hdescent : baseEnd_5194467 < baseStart_5194467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194490 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_5194490 : Nat := 118140960795 + 5194490 * 2 ^ 59
def prefixEnd_5194490 : Nat := 4983230072969 + 3 ^ 40 * 5194490 * 2
def baseEnd_5194490 : Nat := 2667270124973486767685981

theorem tailTrace_5194490 : CollatzResearch.WordTrace tailWord_5194490 prefixEnd_5194490 2667270124973486767685981 := by
  unfold tailWord_5194490
  simp only [CollatzResearch.WordTrace]
  refine ⟨47364653737814338276907231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126305743300838235405085949 47364653737814338276907231)
  ·
    refine ⟨71046980606721507415360847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47364653737814338276907231 71046980606721507415360847)
    ·
      refine ⟨106570470910082261123041271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71046980606721507415360847 106570470910082261123041271)
      ·
        refine ⟨159855706365123391684561907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106570470910082261123041271 159855706365123391684561907)
        ·
          refine ⟨239783559547685087526842861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159855706365123391684561907 239783559547685087526842861)
          ·
            refine ⟨89918834830381907822566073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239783559547685087526842861 89918834830381907822566073)
            ·
              refine ⟨67439126122786430866924555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89918834830381907822566073 67439126122786430866924555)
              ·
                refine ⟨101158689184179646300386833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67439126122786430866924555 101158689184179646300386833)
                ·
                  refine ⟨75869016888134734725290125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101158689184179646300386833 75869016888134734725290125)
                  ·
                    refine ⟨28450881333050525521983797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75869016888134734725290125 28450881333050525521983797)
                    ·
                      refine ⟨2667270124973486767685981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28450881333050525521983797 2667270124973486767685981)
                      ·
                        rfl

theorem cell23_5194490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_5194490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194490 prefixEnd_5194490 := by exact prefixLift 5194490
  have htrace : WordTrace (prefixWord ++ tailWord_5194490) baseStart_5194490 baseEnd_5194490 := by
    simpa [prefixWord, tailWord_5194490, baseEnd_5194490] using wordTrace_append hprefix tailTrace_5194490
  have hstable : (prefixWord ++ tailWord_5194490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194490).length < 2 ^ (prefixWord ++ tailWord_5194490).sum := by decide
  have hdescent : baseEnd_5194490 < baseStart_5194490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194504 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_5194504 : Nat := 118140960795 + 5194504 * 2 ^ 59
def prefixEnd_5194504 : Nat := 4983230072969 + 3 ^ 40 * 5194504 * 2
def baseEnd_5194504 : Nat := 2667277313702649712910917

theorem tailTrace_5194504 : CollatzResearch.WordTrace tailWord_5194504 prefixEnd_5194504 2667277313702649712910917 := by
  unfold tailWord_5194504
  simp only [CollatzResearch.WordTrace]
  refine ⟨94729562786603316749319283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126306083715471088999092377 94729562786603316749319283)
  ·
    refine ⟨142094344179904975123978925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94729562786603316749319283 142094344179904975123978925)
    ·
      refine ⟨53285379067464365671492097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142094344179904975123978925 53285379067464365671492097)
      ·
        refine ⟨39964034300598274253619073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53285379067464365671492097 39964034300598274253619073)
        ·
          refine ⟨29973025725448705690214305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39964034300598274253619073 29973025725448705690214305)
          ·
            refine ⟨22479769294086529267660729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29973025725448705690214305 22479769294086529267660729)
            ·
              refine ⟨16859826970564896950745547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22479769294086529267660729 16859826970564896950745547)
              ·
                refine ⟨25289740455847345426118321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16859826970564896950745547 25289740455847345426118321)
                ·
                  refine ⟨18967305341885509069588741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25289740455847345426118321 18967305341885509069588741)
                  ·
                    refine ⟨3556369751603532950547889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18967305341885509069588741 3556369751603532950547889)
                    ·
                      refine ⟨2667277313702649712910917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556369751603532950547889 2667277313702649712910917)
                      ·
                        rfl

theorem cell23_5194504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_5194504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194504 prefixEnd_5194504 := by exact prefixLift 5194504
  have htrace : WordTrace (prefixWord ++ tailWord_5194504) baseStart_5194504 baseEnd_5194504 := by
    simpa [prefixWord, tailWord_5194504, baseEnd_5194504] using wordTrace_append hprefix tailTrace_5194504
  have hstable : (prefixWord ++ tailWord_5194504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194504).length < 2 ^ (prefixWord ++ tailWord_5194504).sum := by decide
  have hdescent : baseEnd_5194504 < baseStart_5194504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194548 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_5194548 : Nat := 118140960795 + 5194548 * 2 ^ 59
def prefixEnd_5194548 : Nat := 4983230072969 + 3 ^ 40 * 5194548 * 2
def baseEnd_5194548 : Nat := 889099968950482513586905

theorem tailTrace_5194548 : CollatzResearch.WordTrace tailWord_5194548 prefixEnd_5194548 889099968950482513586905 := by
  unfold tailWord_5194548
  simp only [CollatzResearch.WordTrace]
  refine ⟨94730365192523614506620149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126307153590031486008826865 94730365192523614506620149)
  ·
    refine ⟨8880971736799088859995639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94730365192523614506620149 8880971736799088859995639)
    ·
      refine ⟨13321457605198633289993459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8880971736799088859995639 13321457605198633289993459)
      ·
        refine ⟨19982186407797949934990189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13321457605198633289993459 19982186407797949934990189)
        ·
          refine ⟨7493319902924231225621321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19982186407797949934990189 7493319902924231225621321)
          ·
            refine ⟨5619989927193173419215991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7493319902924231225621321 5619989927193173419215991)
            ·
              refine ⟨8429984890789760128823987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619989927193173419215991 8429984890789760128823987)
              ·
                refine ⟨12644977336184640193235981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8429984890789760128823987 12644977336184640193235981)
                ·
                  refine ⟨4741866501069240072463493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12644977336184640193235981 4741866501069240072463493)
                  ·
                    refine ⟨889099968950482513586905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4741866501069240072463493 889099968950482513586905)
                    ·
                      rfl

theorem cell23_5194548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_5194548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194548 prefixEnd_5194548 := by exact prefixLift 5194548
  have htrace : WordTrace (prefixWord ++ tailWord_5194548) baseStart_5194548 baseEnd_5194548 := by
    simpa [prefixWord, tailWord_5194548, baseEnd_5194548] using wordTrace_append hprefix tailTrace_5194548
  have hstable : (prefixWord ++ tailWord_5194548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194548).length < 2 ^ (prefixWord ++ tailWord_5194548).sum := by decide
  have hdescent : baseEnd_5194548 < baseStart_5194548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194561 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 6]
def baseStart_5194561 : Nat := 118140960795 + 5194561 * 2 ^ 59
def prefixEnd_5194561 : Nat := 4983230072969 + 3 ^ 40 * 5194561 * 2
def baseEnd_5194561 : Nat := 296367398011106221099795

theorem tailTrace_5194561 : CollatzResearch.WordTrace tailWord_5194561 prefixEnd_5194561 296367398011106221099795 := by
  unfold tailWord_5194561
  simp only [CollatzResearch.WordTrace]
  refine ⟨189461204534000132233463537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126307469689333421488975691 189461204534000132233463537)
  ·
    refine ⟨142095903400500099175097653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189461204534000132233463537 142095903400500099175097653)
    ·
      refine ⟨13321490943796884297665405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142095903400500099175097653 13321490943796884297665405)
      ·
        refine ⟨4995559103923831611624527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13321490943796884297665405 4995559103923831611624527)
        ·
          refine ⟨7493338655885747417436791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995559103923831611624527 7493338655885747417436791)
          ·
            refine ⟨11240007983828621126155187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493338655885747417436791 11240007983828621126155187)
            ·
              refine ⟨16860011975742931689232781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11240007983828621126155187 16860011975742931689232781)
              ·
                refine ⟨6322504490903599383462293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16860011975742931689232781 6322504490903599383462293)
                ·
                  refine ⟨296367398011106221099795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6322504490903599383462293 296367398011106221099795)
                  ·
                    rfl

theorem cell23_5194561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 6].length) (baseStart_5194561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194561 prefixEnd_5194561 := by exact prefixLift 5194561
  have htrace : WordTrace (prefixWord ++ tailWord_5194561) baseStart_5194561 baseEnd_5194561 := by
    simpa [prefixWord, tailWord_5194561, baseEnd_5194561] using wordTrace_append hprefix tailTrace_5194561
  have hstable : (prefixWord ++ tailWord_5194561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194561).length < 2 ^ (prefixWord ++ tailWord_5194561).sum := by decide
  have hdescent : baseEnd_5194561 < baseStart_5194561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194581 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_5194581 : Nat := 118140960795 + 5194581 * 2 ^ 59
def prefixEnd_5194581 : Nat := 4983230072969 + 3 ^ 40 * 5194581 * 2
def baseEnd_5194581 : Nat := 2667316851713045911648063

theorem tailTrace_5194581 : CollatzResearch.WordTrace tailWord_5194581 prefixEnd_5194581 2667316851713045911648063 := by
  unfold tailWord_5194581
  simp only [CollatzResearch.WordTrace]
  refine ⟨189461933993927675649191597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126307955995951783766127731 189461933993927675649191597)
  ·
    refine ⟨71048225247722878368446849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189461933993927675649191597 71048225247722878368446849)
    ·
      refine ⟨53286168935792158776335137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71048225247722878368446849 53286168935792158776335137)
      ·
        refine ⟨39964626701844119082251353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53286168935792158776335137 39964626701844119082251353)
        ·
          refine ⟨29973470026383089311688515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39964626701844119082251353 29973470026383089311688515)
          ·
            refine ⟨44960205039574633967532773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29973470026383089311688515 44960205039574633967532773)
            ·
              refine ⟨8430038444920243868912395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44960205039574633967532773 8430038444920243868912395)
              ·
                refine ⟨12645057667380365803368593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430038444920243868912395 12645057667380365803368593)
                ·
                  refine ⟨9483793250535274352526445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12645057667380365803368593 9483793250535274352526445)
                  ·
                    refine ⟨3556422468950727882197417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9483793250535274352526445 3556422468950727882197417)
                    ·
                      refine ⟨2667316851713045911648063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556422468950727882197417 2667316851713045911648063)
                      ·
                        rfl

theorem cell23_5194581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_5194581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194581 prefixEnd_5194581 := by exact prefixLift 5194581
  have htrace : WordTrace (prefixWord ++ tailWord_5194581) baseStart_5194581 baseEnd_5194581 := by
    simpa [prefixWord, tailWord_5194581, baseEnd_5194581] using wordTrace_append hprefix tailTrace_5194581
  have hstable : (prefixWord ++ tailWord_5194581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194581).length < 2 ^ (prefixWord ++ tailWord_5194581).sum := by decide
  have hdescent : baseEnd_5194581 < baseStart_5194581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194617 : List Nat := [1, 2, 1, 3, 2, 3, 3, 8]
def baseStart_5194617 : Nat := 118140960795 + 5194617 * 2 ^ 59
def prefixEnd_5194617 : Nat := 4983230072969 + 3 ^ 40 * 5194617 * 2
def baseEnd_5194617 : Nat := 98790197667281769288811

theorem tailTrace_5194617 : CollatzResearch.WordTrace tailWord_5194617 prefixEnd_5194617 98790197667281769288811 := by
  unfold tailWord_5194617
  simp only [CollatzResearch.WordTrace]
  refine ⟨189463247021797253797502105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126308831347864835865001403 189463247021797253797502105)
  ·
    refine ⟨142097435266347940348126579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189463247021797253797502105 142097435266347940348126579)
    ·
      refine ⟨213146152899521910522189869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142097435266347940348126579 213146152899521910522189869)
      ·
        refine ⟨79929807337320716445821201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213146152899521910522189869 79929807337320716445821201)
        ·
          refine ⟨59947355502990537334365901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79929807337320716445821201 59947355502990537334365901)
          ·
            refine ⟨22480258313621451500387213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59947355502990537334365901 22480258313621451500387213)
            ·
              refine ⟨8430096867608044312645205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22480258313621451500387213 8430096867608044312645205)
              ·
                refine ⟨98790197667281769288811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8430096867608044312645205 98790197667281769288811)
                ·
                  rfl

theorem cell23_5194617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 8].length) (baseStart_5194617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194617 prefixEnd_5194617 := by exact prefixLift 5194617
  have htrace : WordTrace (prefixWord ++ tailWord_5194617) baseStart_5194617 baseEnd_5194617 := by
    simpa [prefixWord, tailWord_5194617, baseEnd_5194617] using wordTrace_append hprefix tailTrace_5194617
  have hstable : (prefixWord ++ tailWord_5194617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194617).length < 2 ^ (prefixWord ++ tailWord_5194617).sum := by decide
  have hdescent : baseEnd_5194617 < baseStart_5194617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194645 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_5194645 : Nat := 118140960795 + 5194645 * 2 ^ 59
def prefixEnd_5194645 : Nat := 4983230072969 + 3 ^ 40 * 5194645 * 2
def baseEnd_5194645 : Nat := 2667349714474933661247769

theorem tailTrace_5194645 : CollatzResearch.WordTrace tailWord_5194645 prefixEnd_5194645 2667349714474933661247769 := by
  unfold tailWord_5194645
  simp only [CollatzResearch.WordTrace]
  refine ⟨189464268265695814579521389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126309512177130543053014259 189464268265695814579521389)
  ·
    refine ⟨71049100599635930467320521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189464268265695814579521389 71049100599635930467320521)
    ·
      refine ⟨53286825449726947850490391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71049100599635930467320521 53286825449726947850490391)
      ·
        refine ⟨79930238174590421775735587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53286825449726947850490391 79930238174590421775735587)
        ·
          refine ⟨119895357261885632663603381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79930238174590421775735587 119895357261885632663603381)
          ·
            refine ⟨11240189743301778062212817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119895357261885632663603381 11240189743301778062212817)
            ·
              refine ⟨8430142307476333546659613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11240189743301778062212817 8430142307476333546659613)
              ·
                refine ⟨3161303365303625079997355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8430142307476333546659613 3161303365303625079997355)
                ·
                  refine ⟨4741955047955437619996033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161303365303625079997355 4741955047955437619996033)
                  ·
                    refine ⟨3556466285966578214997025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4741955047955437619996033 3556466285966578214997025)
                    ·
                      refine ⟨2667349714474933661247769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556466285966578214997025 2667349714474933661247769)
                      ·
                        rfl

theorem cell23_5194645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_5194645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194645 prefixEnd_5194645 := by exact prefixLift 5194645
  have htrace : WordTrace (prefixWord ++ tailWord_5194645) baseStart_5194645 baseEnd_5194645 := by
    simpa [prefixWord, tailWord_5194645, baseEnd_5194645] using wordTrace_append hprefix tailTrace_5194645
  have hstable : (prefixWord ++ tailWord_5194645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194645).length < 2 ^ (prefixWord ++ tailWord_5194645).sum := by decide
  have hdescent : baseEnd_5194645 < baseStart_5194645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194688 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 1, 3, 2]
def baseStart_5194688 : Nat := 118140960795 + 5194688 * 2 ^ 59
def prefixEnd_5194688 : Nat := 4983230072969 + 3 ^ 40 * 5194688 * 2
def baseEnd_5194688 : Nat := 2667371794143076993010071

theorem tailTrace_5194688 : CollatzResearch.WordTrace tailWord_5194688 prefixEnd_5194688 2667371794143076993010071 := by
  unfold tailWord_5194688
  simp only [CollatzResearch.WordTrace]
  refine ⟨94732918302270016461668359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126310557736360021948891145 94732918302270016461668359)
  ·
    refine ⟨142099377453405024692502539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94732918302270016461668359 142099377453405024692502539)
    ·
      refine ⟨213149066180107537038753809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142099377453405024692502539 213149066180107537038753809)
      ·
        refine ⟨159861799635080652779065357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213149066180107537038753809 159861799635080652779065357)
        ·
          refine ⟨59948174863155244792149509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159861799635080652779065357 59948174863155244792149509)
          ·
            refine ⟨11240282786841608398528033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59948174863155244792149509 11240282786841608398528033)
            ·
              refine ⟨8430212090131206298896025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11240282786841608398528033 8430212090131206298896025)
              ·
                refine ⟨6322659067598404724172019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8430212090131206298896025 6322659067598404724172019)
                ·
                  refine ⟨9483988601397607086258029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6322659067598404724172019 9483988601397607086258029)
                  ·
                    refine ⟨3556495725524102657346761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9483988601397607086258029 3556495725524102657346761)
                    ·
                      refine ⟨2667371794143076993010071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556495725524102657346761 2667371794143076993010071)
                      ·
                        rfl

theorem cell23_5194688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_5194688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194688 prefixEnd_5194688 := by exact prefixLift 5194688
  have htrace : WordTrace (prefixWord ++ tailWord_5194688) baseStart_5194688 baseEnd_5194688 := by
    simpa [prefixWord, tailWord_5194688, baseEnd_5194688] using wordTrace_append hprefix tailTrace_5194688
  have hstable : (prefixWord ++ tailWord_5194688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194688).length < 2 ^ (prefixWord ++ tailWord_5194688).sum := by decide
  have hdescent : baseEnd_5194688 < baseStart_5194688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194735 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 2, 2, 2]
def baseStart_5194735 : Nat := 118140960795 + 5194735 * 2 ^ 59
def prefixEnd_5194735 : Nat := 4983230072969 + 3 ^ 40 * 5194735 * 2
def baseEnd_5194735 : Nat := 2667395927733838309122355

theorem tailTrace_5194735 : CollatzResearch.WordTrace tailWord_5194735 prefixEnd_5194735 2667395927733838309122355 := by
  unfold tailWord_5194735
  simp only [CollatzResearch.WordTrace]
  refine ⟨189467550835369759950297659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126311700556913173300198439 189467550835369759950297659)
  ·
    refine ⟨284201326253054639925446489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189467550835369759950297659 284201326253054639925446489)
    ·
      refine ⟨213150994689790979944084867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284201326253054639925446489 213150994689790979944084867)
      ·
        refine ⟨319726492034686469916127301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213150994689790979944084867 319726492034686469916127301)
        ·
          refine ⟨59948717256503713109273869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319726492034686469916127301 59948717256503713109273869)
          ·
            refine ⟨22480768971188892415977701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59948717256503713109273869 22480768971188892415977701)
            ·
              refine ⟨4215144182097917327995819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22480768971188892415977701 4215144182097917327995819)
              ·
                refine ⟨6322716273146875991993729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4215144182097917327995819 6322716273146875991993729)
                ·
                  refine ⟨4742037204860156993995297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6322716273146875991993729 4742037204860156993995297)
                  ·
                    refine ⟨3556527903645117745496473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4742037204860156993995297 3556527903645117745496473)
                    ·
                      refine ⟨2667395927733838309122355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556527903645117745496473 2667395927733838309122355)
                      ·
                        rfl

theorem cell23_5194735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 2, 2, 2].length) (baseStart_5194735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194735 prefixEnd_5194735 := by exact prefixLift 5194735
  have htrace : WordTrace (prefixWord ++ tailWord_5194735) baseStart_5194735 baseEnd_5194735 := by
    simpa [prefixWord, tailWord_5194735, baseEnd_5194735] using wordTrace_append hprefix tailTrace_5194735
  have hstable : (prefixWord ++ tailWord_5194735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194735).length < 2 ^ (prefixWord ++ tailWord_5194735).sum := by decide
  have hdescent : baseEnd_5194735 < baseStart_5194735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194747 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_5194747 : Nat := 118140960795 + 5194747 * 2 ^ 59
def prefixEnd_5194747 : Nat := 4983230072969 + 3 ^ 40 * 5194747 * 2
def baseEnd_5194747 : Nat := 2667402089501692262172299

theorem tailTrace_5194747 : CollatzResearch.WordTrace tailWord_5194747 prefixEnd_5194747 2667402089501692262172299 := by
  unfold tailWord_5194747
  simp only [CollatzResearch.WordTrace]
  refine ⟨189467988511326285999734495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126311992340884190666489663 189467988511326285999734495)
  ·
    refine ⟨284201982766989428999601743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189467988511326285999734495 284201982766989428999601743)
    ·
      refine ⟨426302974150484143499402615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284201982766989428999601743 426302974150484143499402615)
      ·
        refine ⟨639454461225726215249103923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426302974150484143499402615 639454461225726215249103923)
        ·
          refine ⟨959181691838589322873655885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639454461225726215249103923 959181691838589322873655885)
          ·
            refine ⟨359693134439470996077620957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 959181691838589322873655885 359693134439470996077620957)
            ·
              refine ⟨134884925414801623529107859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359693134439470996077620957 134884925414801623529107859)
              ·
                refine ⟨202327388122202435293661789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134884925414801623529107859 202327388122202435293661789)
                ·
                  refine ⟨75872770545825913235123171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202327388122202435293661789 75872770545825913235123171)
                  ·
                    refine ⟨113809155818738869852684757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75872770545825913235123171 113809155818738869852684757)
                    ·
                      refine ⟨2667402089501692262172299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113809155818738869852684757 2667402089501692262172299)
                      ·
                        rfl

theorem cell23_5194747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_5194747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194747 prefixEnd_5194747 := by exact prefixLift 5194747
  have htrace : WordTrace (prefixWord ++ tailWord_5194747) baseStart_5194747 baseEnd_5194747 := by
    simpa [prefixWord, tailWord_5194747, baseEnd_5194747] using wordTrace_append hprefix tailTrace_5194747
  have hstable : (prefixWord ++ tailWord_5194747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194747).length < 2 ^ (prefixWord ++ tailWord_5194747).sum := by decide
  have hdescent : baseEnd_5194747 < baseStart_5194747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194764 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_5194764 : Nat := 118140960795 + 5194764 * 2 ^ 59
def prefixEnd_5194764 : Nat := 4983230072969 + 3 ^ 40 * 5194764 * 2
def baseEnd_5194764 : Nat := 2667410818672818695659721

theorem tailTrace_5194764 : CollatzResearch.WordTrace tailWord_5194764 prefixEnd_5194764 2667410818672818695659721 := by
  unfold tailWord_5194764
  simp only [CollatzResearch.WordTrace]
  refine ⟨94734304276132348951551673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126312405701509798602068897 94734304276132348951551673)
  ·
    refine ⟨71050728207099261713663755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94734304276132348951551673 71050728207099261713663755)
    ·
      refine ⟨106576092310648892570495633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71050728207099261713663755 106576092310648892570495633)
      ·
        refine ⟨79932069232986669427871725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106576092310648892570495633 79932069232986669427871725)
        ·
          refine ⟨29974525962370001035451897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79932069232986669427871725 29974525962370001035451897)
          ·
            refine ⟨22480894471777500776588923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29974525962370001035451897 22480894471777500776588923)
            ·
              refine ⟨33721341707666251164883385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22480894471777500776588923 33721341707666251164883385)
              ·
                refine ⟨25291006280749688373662539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33721341707666251164883385 25291006280749688373662539)
                ·
                  refine ⟨37936509421124532560493809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25291006280749688373662539 37936509421124532560493809)
                  ·
                    refine ⟨28452382065843399420370357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37936509421124532560493809 28452382065843399420370357)
                    ·
                      refine ⟨2667410818672818695659721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28452382065843399420370357 2667410818672818695659721)
                      ·
                        rfl

theorem cell23_5194764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_5194764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194764 prefixEnd_5194764 := by exact prefixLift 5194764
  have htrace : WordTrace (prefixWord ++ tailWord_5194764) baseStart_5194764 baseEnd_5194764 := by
    simpa [prefixWord, tailWord_5194764, baseEnd_5194764] using wordTrace_append hprefix tailTrace_5194764
  have hstable : (prefixWord ++ tailWord_5194764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194764).length < 2 ^ (prefixWord ++ tailWord_5194764).sum := by decide
  have hdescent : baseEnd_5194764 < baseStart_5194764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194767 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 10]
def baseStart_5194767 : Nat := 118140960795 + 5194767 * 2 ^ 59
def prefixEnd_5194767 : Nat := 4983230072969 + 3 ^ 40 * 5194767 * 2
def baseEnd_5194767 : Nat := 889137453038260727974069

theorem tailTrace_5194767 : CollatzResearch.WordTrace tailWord_5194767 prefixEnd_5194767 889137453038260727974069 := by
  unfold tailWord_5194767
  simp only [CollatzResearch.WordTrace]
  refine ⟨189468717971253829415462555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126312478647502552943641703 189468717971253829415462555)
  ·
    refine ⟨284203076956880744123193833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189468717971253829415462555 284203076956880744123193833)
    ·
      refine ⟨213152307717660558092395375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284203076956880744123193833 213152307717660558092395375)
      ·
        refine ⟨319728461576490837138593063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213152307717660558092395375 319728461576490837138593063)
        ·
          refine ⟨479592692364736255707889595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319728461576490837138593063 479592692364736255707889595)
          ·
            refine ⟨719389038547104383561834393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479592692364736255707889595 719389038547104383561834393)
            ·
              refine ⟨539541778910328287671375795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719389038547104383561834393 539541778910328287671375795)
              ·
                refine ⟨809312668365492431507063693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539541778910328287671375795 809312668365492431507063693)
                ·
                  refine ⟨303492250637059661815148885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809312668365492431507063693 303492250637059661815148885)
                  ·
                    refine ⟨889137453038260727974069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 303492250637059661815148885 889137453038260727974069)
                    ·
                      rfl

theorem cell23_5194767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_5194767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194767 prefixEnd_5194767 := by exact prefixLift 5194767
  have htrace : WordTrace (prefixWord ++ tailWord_5194767) baseStart_5194767 baseEnd_5194767 := by
    simpa [prefixWord, tailWord_5194767, baseEnd_5194767] using wordTrace_append hprefix tailTrace_5194767
  have hstable : (prefixWord ++ tailWord_5194767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194767).length < 2 ^ (prefixWord ++ tailWord_5194767).sum := by decide
  have hdescent : baseEnd_5194767 < baseStart_5194767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194775 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 5]
def baseStart_5194775 : Nat := 118140960795 + 5194775 * 2 ^ 59
def prefixEnd_5194775 : Nat := 4983230072969 + 3 ^ 40 * 5194775 * 2
def baseEnd_5194775 : Nat := 296379607440002016958019

theorem tailTrace_5194775 : CollatzResearch.WordTrace tailWord_5194775 prefixEnd_5194775 296379607440002016958019 := by
  unfold tailWord_5194775
  simp only [CollatzResearch.WordTrace]
  refine ⟨189469009755224846781753779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126312673170149897854502519 189469009755224846781753779)
  ·
    refine ⟨284203514632837270172630669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189469009755224846781753779 284203514632837270172630669)
    ·
      refine ⟨106576317987313976314736501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284203514632837270172630669 106576317987313976314736501)
      ·
        refine ⟨9991529811310685279506547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106576317987313976314736501 9991529811310685279506547)
        ·
          refine ⟨14987294716966027919259821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9991529811310685279506547 14987294716966027919259821)
          ·
            refine ⟨5620235518862260469722433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14987294716966027919259821 5620235518862260469722433)
            ·
              refine ⟨4215176639146695352291825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5620235518862260469722433 4215176639146695352291825)
              ·
                refine ⟨3161382479360021514218869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215176639146695352291825 3161382479360021514218869)
                ·
                  refine ⟨296379607440002016958019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3161382479360021514218869 296379607440002016958019)
                  ·
                    rfl

theorem cell23_5194775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 5].length) (baseStart_5194775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194775 prefixEnd_5194775 := by exact prefixLift 5194775
  have htrace : WordTrace (prefixWord ++ tailWord_5194775) baseStart_5194775 baseEnd_5194775 := by
    simpa [prefixWord, tailWord_5194775, baseEnd_5194775] using wordTrace_append hprefix tailTrace_5194775
  have hstable : (prefixWord ++ tailWord_5194775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194775).length < 2 ^ (prefixWord ++ tailWord_5194775).sum := by decide
  have hdescent : baseEnd_5194775 < baseStart_5194775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194801 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 3, 4]
def baseStart_5194801 : Nat := 118140960795 + 5194801 * 2 ^ 59
def prefixEnd_5194801 : Nat := 4983230072969 + 3 ^ 40 * 5194801 * 2
def baseEnd_5194801 : Nat := 889143272485678350299017

theorem tailTrace_5194801 : CollatzResearch.WordTrace tailWord_5194801 prefixEnd_5194801 889143272485678350299017 := by
  unfold tailWord_5194801
  simp only [CollatzResearch.WordTrace]
  refine ⟨189469958053130653222200257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126313305368753768814800171 189469958053130653222200257)
  ·
    refine ⟨142102468539847989916650193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189469958053130653222200257 142102468539847989916650193)
    ·
      refine ⟨106576851404885992437487645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142102468539847989916650193 106576851404885992437487645)
      ·
        refine ⟨39966319276832247164057867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106576851404885992437487645 39966319276832247164057867)
        ·
          refine ⟨59949478915248370746086801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39966319276832247164057867 59949478915248370746086801)
          ·
            refine ⟨44962109186436278059565101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59949478915248370746086801 44962109186436278059565101)
            ·
              refine ⟨16860790944913604272336913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44962109186436278059565101 16860790944913604272336913)
              ·
                refine ⟨12645593208685203204252685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16860790944913604272336913 12645593208685203204252685)
                ·
                  refine ⟨4742097453256951201594757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12645593208685203204252685 4742097453256951201594757)
                  ·
                    refine ⟨889143272485678350299017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4742097453256951201594757 889143272485678350299017)
                    ·
                      rfl

theorem cell23_5194801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_5194801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194801 prefixEnd_5194801 := by exact prefixLift 5194801
  have htrace : WordTrace (prefixWord ++ tailWord_5194801) baseStart_5194801 baseEnd_5194801 := by
    simpa [prefixWord, tailWord_5194801, baseEnd_5194801] using wordTrace_append hprefix tailTrace_5194801
  have hstable : (prefixWord ++ tailWord_5194801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194801).length < 2 ^ (prefixWord ++ tailWord_5194801).sum := by decide
  have hdescent : baseEnd_5194801 < baseStart_5194801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194808 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_5194808 : Nat := 118140960795 + 5194808 * 2 ^ 59
def prefixEnd_5194808 : Nat := 4983230072969 + 3 ^ 40 * 5194808 * 2
def baseEnd_5194808 : Nat := 2667433411821616523509519

theorem tailTrace_5194808 : CollatzResearch.WordTrace tailWord_5194808 prefixEnd_5194808 2667433411821616523509519 := by
  unfold tailWord_5194808
  simp only [CollatzResearch.WordTrace]
  refine ⟨94735106682052646708852539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126313475576070195611803385 94735106682052646708852539)
  ·
    refine ⟨142102660023078970063278809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94735106682052646708852539 142102660023078970063278809)
    ·
      refine ⟨106576995017309227547459107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142102660023078970063278809 106576995017309227547459107)
      ·
        refine ⟨159865492525963841321188661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106576995017309227547459107 159865492525963841321188661)
        ·
          refine ⟨14987389924309110123861437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159865492525963841321188661 14987389924309110123861437)
          ·
            refine ⟨5620271221615916296448039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14987389924309110123861437 5620271221615916296448039)
            ·
              refine ⟨8430406832423874444672059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620271221615916296448039 8430406832423874444672059)
              ·
                refine ⟨12645610248635811667008089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430406832423874444672059 12645610248635811667008089)
                ·
                  refine ⟨9484207686476858750256067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12645610248635811667008089 9484207686476858750256067)
                  ·
                    refine ⟨14226311529715288125384101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9484207686476858750256067 14226311529715288125384101)
                    ·
                      refine ⟨2667433411821616523509519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14226311529715288125384101 2667433411821616523509519)
                      ·
                        rfl

theorem cell23_5194808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_5194808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194808 prefixEnd_5194808 := by exact prefixLift 5194808
  have htrace : WordTrace (prefixWord ++ tailWord_5194808) baseStart_5194808 baseEnd_5194808 := by
    simpa [prefixWord, tailWord_5194808, baseEnd_5194808] using wordTrace_append hprefix tailTrace_5194808
  have hstable : (prefixWord ++ tailWord_5194808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194808).length < 2 ^ (prefixWord ++ tailWord_5194808).sum := by decide
  have hdescent : baseEnd_5194808 < baseStart_5194808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194869 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_5194869 : Nat := 118140960795 + 5194869 * 2 ^ 59
def prefixEnd_5194869 : Nat := 4983230072969 + 3 ^ 40 * 5194869 * 2
def baseEnd_5194869 : Nat := 889154911380513594948913

theorem tailTrace_5194869 : CollatzResearch.WordTrace tailWord_5194869 prefixEnd_5194869 889154911380513594948913 := by
  unfold tailWord_5194869
  simp only [CollatzResearch.WordTrace]
  refine ⟨189472438216884300835675661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126314958811256200557117107 189472438216884300835675661)
  ·
    refine ⟨71052164331331612813378373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189472438216884300835675661 71052164331331612813378373)
    ·
      refine ⟨13322280812124677402508445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71052164331331612813378373 13322280812124677402508445)
      ·
        refine ⟨4995855304546754025940667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13322280812124677402508445 4995855304546754025940667)
        ·
          refine ⟨7493782956820131038911001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995855304546754025940667 7493782956820131038911001)
          ·
            refine ⟨5620337217615098279183251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7493782956820131038911001 5620337217615098279183251)
            ·
              refine ⟨8430505826422647418774877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620337217615098279183251 8430505826422647418774877)
              ·
                refine ⟨3161439684908492782040579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8430505826422647418774877 3161439684908492782040579)
                ·
                  refine ⟨4742159527362739173060869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161439684908492782040579 4742159527362739173060869)
                  ·
                    refine ⟨889154911380513594948913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4742159527362739173060869 889154911380513594948913)
                    ·
                      rfl

theorem cell23_5194869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_5194869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194869 prefixEnd_5194869 := by exact prefixLift 5194869
  have htrace : WordTrace (prefixWord ++ tailWord_5194869) baseStart_5194869 baseEnd_5194869 := by
    simpa [prefixWord, tailWord_5194869, baseEnd_5194869] using wordTrace_append hprefix tailTrace_5194869
  have hstable : (prefixWord ++ tailWord_5194869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194869).length < 2 ^ (prefixWord ++ tailWord_5194869).sum := by decide
  have hdescent : baseEnd_5194869 < baseStart_5194869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194885 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 2, 3, 2]
def baseStart_5194885 : Nat := 118140960795 + 5194885 * 2 ^ 59
def prefixEnd_5194885 : Nat := 4983230072969 + 3 ^ 40 * 5194885 * 2
def baseEnd_5194885 : Nat := 2667472949832012722246665

theorem tailTrace_5194885 : CollatzResearch.WordTrace tailWord_5194885 prefixEnd_5194885 2667472949832012722246665 := by
  unfold tailWord_5194885
  simp only [CollatzResearch.WordTrace]
  refine ⟨189473021784826335568258109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126315347856550890378838739 189473021784826335568258109)
  ·
    refine ⟨71052383169309875838096791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189473021784826335568258109 71052383169309875838096791)
    ·
      refine ⟨106578574753964813757145187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71052383169309875838096791 106578574753964813757145187)
      ·
        refine ⟨159867862130947220635717781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106578574753964813757145187 159867862130947220635717781)
        ·
          refine ⟨7493806037388150967299271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159867862130947220635717781 7493806037388150967299271)
          ·
            refine ⟨11240709056082226450948907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493806037388150967299271 11240709056082226450948907)
            ·
              refine ⟨16861063584123339676423361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11240709056082226450948907 16861063584123339676423361)
              ·
                refine ⟨12645797688092504757317521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16861063584123339676423361 12645797688092504757317521)
                ·
                  refine ⟨9484348266069378567988141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12645797688092504757317521 9484348266069378567988141)
                  ·
                    refine ⟨3556630599776016962995553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9484348266069378567988141 3556630599776016962995553)
                    ·
                      refine ⟨2667472949832012722246665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556630599776016962995553 2667472949832012722246665)
                      ·
                        rfl

theorem cell23_5194885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_5194885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194885 prefixEnd_5194885 := by exact prefixLift 5194885
  have htrace : WordTrace (prefixWord ++ tailWord_5194885) baseStart_5194885 baseEnd_5194885 := by
    simpa [prefixWord, tailWord_5194885, baseEnd_5194885] using wordTrace_append hprefix tailTrace_5194885
  have hstable : (prefixWord ++ tailWord_5194885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194885).length < 2 ^ (prefixWord ++ tailWord_5194885).sum := by decide
  have hdescent : baseEnd_5194885 < baseStart_5194885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194931 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 3]
def baseStart_5194931 : Nat := 118140960795 + 5194931 * 2 ^ 59
def prefixEnd_5194931 : Nat := 4983230072969 + 3 ^ 40 * 5194931 * 2
def baseEnd_5194931 : Nat := 2667496569942119542271453

theorem tailTrace_5194931 : CollatzResearch.WordTrace tailWord_5194931 prefixEnd_5194931 2667496569942119542271453 := by
  unfold tailWord_5194931
  simp only [CollatzResearch.WordTrace]
  refine ⟨189474699542659685424432647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126316466361773123616288431 189474699542659685424432647)
  ·
    refine ⟨284212049313989528136648971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189474699542659685424432647 284212049313989528136648971)
    ·
      refine ⟨426318073970984292204973457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284212049313989528136648971 426318073970984292204973457)
      ·
        refine ⟨319738555478238219153730093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426318073970984292204973457 319738555478238219153730093)
        ·
          refine ⟨119901958304339332182648785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319738555478238219153730093 119901958304339332182648785)
          ·
            refine ⟨89926468728254499136986589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119901958304339332182648785 89926468728254499136986589)
            ·
              refine ⟨33722425773095437176369971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89926468728254499136986589 33722425773095437176369971)
              ·
                refine ⟨50583638659643155764554957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33722425773095437176369971 50583638659643155764554957)
                ·
                  refine ⟨18968864497366183411708109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50583638659643155764554957 18968864497366183411708109)
                  ·
                    refine ⟨7113324186512318779390541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18968864497366183411708109 7113324186512318779390541)
                    ·
                      refine ⟨2667496569942119542271453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7113324186512318779390541 2667496569942119542271453)
                      ·
                        rfl

theorem cell23_5194931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_5194931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194931 prefixEnd_5194931 := by exact prefixLift 5194931
  have htrace : WordTrace (prefixWord ++ tailWord_5194931) baseStart_5194931 baseEnd_5194931 := by
    simpa [prefixWord, tailWord_5194931, baseEnd_5194931] using wordTrace_append hprefix tailTrace_5194931
  have hstable : (prefixWord ++ tailWord_5194931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194931).length < 2 ^ (prefixWord ++ tailWord_5194931).sum := by decide
  have hdescent : baseEnd_5194931 < baseStart_5194931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194935 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 1, 2, 3]
def baseStart_5194935 : Nat := 118140960795 + 5194935 * 2 ^ 59
def prefixEnd_5194935 : Nat := 4983230072969 + 3 ^ 40 * 5194935 * 2
def baseEnd_5194935 : Nat := 2667498623864737526621435

theorem tailTrace_5194935 : CollatzResearch.WordTrace tailWord_5194935 prefixEnd_5194935 2667498623864737526621435 := by
  unfold tailWord_5194935
  simp only [CollatzResearch.WordTrace]
  refine ⟨189474845434645194107578259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126316563623096796071718839 189474845434645194107578259)
  ·
    refine ⟨284212268151967791161367389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189474845434645194107578259 284212268151967791161367389)
    ·
      refine ⟨106579600556987921685512771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284212268151967791161367389 106579600556987921685512771)
      ·
        refine ⟨159869400835481882528269157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106579600556987921685512771 159869400835481882528269157)
        ·
          refine ⟨29975512656652852974050467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159869400835481882528269157 29975512656652852974050467)
          ·
            refine ⟨44963268984979279461075701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29975512656652852974050467 44963268984979279461075701)
            ·
              refine ⟨4215306467341807449475847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44963268984979279461075701 4215306467341807449475847)
              ·
                refine ⟨6322959701012711174213771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4215306467341807449475847 6322959701012711174213771)
                ·
                  refine ⟨9484439551519066761320657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6322959701012711174213771 9484439551519066761320657)
                  ·
                    refine ⟨7113329663639300070990493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9484439551519066761320657 7113329663639300070990493)
                    ·
                      refine ⟨2667498623864737526621435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7113329663639300070990493 2667498623864737526621435)
                      ·
                        rfl

theorem cell23_5194935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_5194935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194935 prefixEnd_5194935 := by exact prefixLift 5194935
  have htrace : WordTrace (prefixWord ++ tailWord_5194935) baseStart_5194935 baseEnd_5194935 := by
    simpa [prefixWord, tailWord_5194935, baseEnd_5194935] using wordTrace_append hprefix tailTrace_5194935
  have hstable : (prefixWord ++ tailWord_5194935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194935).length < 2 ^ (prefixWord ++ tailWord_5194935).sum := by decide
  have hdescent : baseEnd_5194935 < baseStart_5194935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5194965 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5194965 : Nat := 118140960795 + 5194965 * 2 ^ 59
def prefixEnd_5194965 : Nat := 4983230072969 + 3 ^ 40 * 5194965 * 2
def baseEnd_5194965 : Nat := 2667514028284372409246297

theorem tailTrace_5194965 : CollatzResearch.WordTrace tailWord_5194965 prefixEnd_5194965 2667514028284372409246297 := by
  unfold tailWord_5194965
  simp only [CollatzResearch.WordTrace]
  refine ⟨189475939624536509231170349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126317293083024339487446899 189475939624536509231170349)
  ·
    refine ⟨71053477359201190961688881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189475939624536509231170349 71053477359201190961688881)
    ·
      refine ⟨53290108019400893221266661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71053477359201190961688881 53290108019400893221266661)
      ·
        refine ⟨9991895253637667478987499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53290108019400893221266661 9991895253637667478987499)
        ·
          refine ⟨14987842880456501218481249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9991895253637667478987499 14987842880456501218481249)
          ·
            refine ⟨11240882160342375913860937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14987842880456501218481249 11240882160342375913860937)
            ·
              refine ⟨8430661620256781935395703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11240882160342375913860937 8430661620256781935395703)
              ·
                refine ⟨12645992430385172903093555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430661620256781935395703 12645992430385172903093555)
                ·
                  refine ⟨18968988645577759354640333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12645992430385172903093555 18968988645577759354640333)
                  ·
                    refine ⟨7113370742091659757990125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18968988645577759354640333 7113370742091659757990125)
                    ·
                      refine ⟨2667514028284372409246297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7113370742091659757990125 2667514028284372409246297)
                      ·
                        rfl

theorem cell23_5194965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5194965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5194965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5194965 prefixEnd_5194965 := by exact prefixLift 5194965
  have htrace : WordTrace (prefixWord ++ tailWord_5194965) baseStart_5194965 baseEnd_5194965 := by
    simpa [prefixWord, tailWord_5194965, baseEnd_5194965] using wordTrace_append hprefix tailTrace_5194965
  have hstable : (prefixWord ++ tailWord_5194965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5194965).length < 2 ^ (prefixWord ++ tailWord_5194965).sum := by decide
  have hdescent : baseEnd_5194965 < baseStart_5194965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5194965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195001 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_5195001 : Nat := 118140960795 + 5195001 * 2 ^ 59
def prefixEnd_5195001 : Nat := 4983230072969 + 3 ^ 40 * 5195001 * 2
def baseEnd_5195001 : Nat := 2667532513587934268396131

theorem tailTrace_5195001 : CollatzResearch.WordTrace tailWord_5195001 prefixEnd_5195001 2667532513587934268396131 := by
  unfold tailWord_5195001
  simp only [CollatzResearch.WordTrace]
  refine ⟨189477252652406087379480857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126318168434937391586320571 189477252652406087379480857)
  ·
    refine ⟨142107939489304565534610643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189477252652406087379480857 142107939489304565534610643)
    ·
      refine ⟨213161909233956848301915965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142107939489304565534610643 213161909233956848301915965)
      ·
        refine ⟨79935715962733818113218487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213161909233956848301915965 79935715962733818113218487)
        ·
          refine ⟨119903573944100727169827731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79935715962733818113218487 119903573944100727169827731)
          ·
            refine ⟨179855360916151090754741597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119903573944100727169827731 179855360916151090754741597)
            ·
              refine ⟨67445760343556659033028099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179855360916151090754741597 67445760343556659033028099)
              ·
                refine ⟨101168640515334988549542149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67445760343556659033028099 101168640515334988549542149)
                ·
                  refine ⟨18969120096625310353039153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101168640515334988549542149 18969120096625310353039153)
                  ·
                    refine ⟨14226840072468982764779365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18969120096625310353039153 14226840072468982764779365)
                    ·
                      refine ⟨2667532513587934268396131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14226840072468982764779365 2667532513587934268396131)
                      ·
                        rfl

theorem cell23_5195001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_5195001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195001 prefixEnd_5195001 := by exact prefixLift 5195001
  have htrace : WordTrace (prefixWord ++ tailWord_5195001) baseStart_5195001 baseEnd_5195001 := by
    simpa [prefixWord, tailWord_5195001, baseEnd_5195001] using wordTrace_append hprefix tailTrace_5195001
  have hstable : (prefixWord ++ tailWord_5195001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195001).length < 2 ^ (prefixWord ++ tailWord_5195001).sum := by decide
  have hdescent : baseEnd_5195001 < baseStart_5195001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195011 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 7]
def baseStart_5195011 : Nat := 118140960795 + 5195011 * 2 ^ 59
def prefixEnd_5195011 : Nat := 4983230072969 + 3 ^ 40 * 5195011 * 2
def baseEnd_5195011 : Nat := 296393072043831025474565

theorem tailTrace_5195011 : CollatzResearch.WordTrace tailWord_5195011 prefixEnd_5195011 296393072043831025474565 := by
  unfold tailWord_5195011
  simp only [CollatzResearch.WordTrace]
  refine ⟨189477617382369859087344887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126318411588246572724896591 189477617382369859087344887)
  ·
    refine ⟨284216426073554788631017331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189477617382369859087344887 284216426073554788631017331)
    ·
      refine ⟨426324639110332182946525997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284216426073554788631017331 426324639110332182946525997)
      ·
        refine ⟨159871739666374568604947249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426324639110332182946525997 159871739666374568604947249)
        ·
          refine ⟨119903804749780926453710437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159871739666374568604947249 119903804749780926453710437)
          ·
            refine ⟨22481963390583923710070707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119903804749780926453710437 22481963390583923710070707)
            ·
              refine ⟨33722945085875885565106061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22481963390583923710070707 33722945085875885565106061)
              ·
                refine ⟨12646104407203457086914773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33722945085875885565106061 12646104407203457086914773)
                ·
                  refine ⟨296393072043831025474565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12646104407203457086914773 296393072043831025474565)
                  ·
                    rfl

theorem cell23_5195011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 7].length) (baseStart_5195011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195011 prefixEnd_5195011 := by exact prefixLift 5195011
  have htrace : WordTrace (prefixWord ++ tailWord_5195011) baseStart_5195011 baseEnd_5195011 := by
    simpa [prefixWord, tailWord_5195011, baseEnd_5195011] using wordTrace_append hprefix tailTrace_5195011
  have hstable : (prefixWord ++ tailWord_5195011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195011).length < 2 ^ (prefixWord ++ tailWord_5195011).sum := by decide
  have hdescent : baseEnd_5195011 < baseStart_5195011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195022 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_5195022 : Nat := 118140960795 + 5195022 * 2 ^ 59
def prefixEnd_5195022 : Nat := 4983230072969 + 3 ^ 40 * 5195022 * 2
def baseEnd_5195022 : Nat := 2667543296681678686233535

theorem tailTrace_5195022 : CollatzResearch.WordTrace tailWord_5195022 prefixEnd_5195022 2667543296681678686233535 := by
  unfold tailWord_5195022
  simp only [CollatzResearch.WordTrace]
  refine ⟨23684752323166250995749415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126318679056886671977330213 23684752323166250995749415)
  ·
    refine ⟨35527128484749376493624123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23684752323166250995749415 35527128484749376493624123)
    ·
      refine ⟨53290692727124064740436185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35527128484749376493624123 53290692727124064740436185)
      ·
        refine ⟨39968019545343048555327139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53290692727124064740436185 39968019545343048555327139)
        ·
          refine ⟨59952029318014572832990709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39968019545343048555327139 59952029318014572832990709)
          ·
            refine ⟨5620502748563866203092879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59952029318014572832990709 5620502748563866203092879)
            ·
              refine ⟨8430754122845799304639319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620502748563866203092879 8430754122845799304639319)
              ·
                refine ⟨12646131184268698956958979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430754122845799304639319 12646131184268698956958979)
                ·
                  refine ⟨18969196776403048435438469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12646131184268698956958979 18969196776403048435438469)
                  ·
                    refine ⟨3556724395575571581644713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18969196776403048435438469 3556724395575571581644713)
                    ·
                      refine ⟨2667543296681678686233535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556724395575571581644713 2667543296681678686233535)
                      ·
                        rfl

theorem cell23_5195022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_5195022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195022 prefixEnd_5195022 := by exact prefixLift 5195022
  have htrace : WordTrace (prefixWord ++ tailWord_5195022) baseStart_5195022 baseEnd_5195022 := by
    simpa [prefixWord, tailWord_5195022, baseEnd_5195022] using wordTrace_append hprefix tailTrace_5195022
  have hstable : (prefixWord ++ tailWord_5195022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195022).length < 2 ^ (prefixWord ++ tailWord_5195022).sum := by decide
  have hdescent : baseEnd_5195022 < baseStart_5195022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195026 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5195026 : Nat := 118140960795 + 5195026 * 2 ^ 59
def prefixEnd_5195026 : Nat := 4983230072969 + 3 ^ 40 * 5195026 * 2
def baseEnd_5195026 : Nat := 2667545350604296670583517

theorem tailTrace_5195026 : CollatzResearch.WordTrace tailWord_5195026 prefixEnd_5195026 2667545350604296670583517 := by
  unfold tailWord_5195026
  simp only [CollatzResearch.WordTrace]
  refine ⟨47369541119328879162285233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126318776318210344432760621 47369541119328879162285233)
  ·
    refine ⟨35527155839496659371713925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47369541119328879162285233 35527155839496659371713925)
    ·
      refine ⟨6661341719905623632196361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35527155839496659371713925 6661341719905623632196361)
      ·
        refine ⟨4996006289929217724147271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6661341719905623632196361 4996006289929217724147271)
        ·
          refine ⟨7494009434893826586220907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4996006289929217724147271 7494009434893826586220907)
          ·
            refine ⟨11241014152340739879331361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494009434893826586220907 11241014152340739879331361)
            ·
              refine ⟨8430760614255554909498521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11241014152340739879331361 8430760614255554909498521)
              ·
                refine ⟨6323070460691666182123891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8430760614255554909498521 6323070460691666182123891)
                ·
                  refine ⟨9484605691037499273185837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6323070460691666182123891 9484605691037499273185837)
                  ·
                    refine ⟨3556727134139062227444689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9484605691037499273185837 3556727134139062227444689)
                    ·
                      refine ⟨2667545350604296670583517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556727134139062227444689 2667545350604296670583517)
                      ·
                        rfl

theorem cell23_5195026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5195026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195026 prefixEnd_5195026 := by exact prefixLift 5195026
  have htrace : WordTrace (prefixWord ++ tailWord_5195026) baseStart_5195026 baseEnd_5195026 := by
    simpa [prefixWord, tailWord_5195026, baseEnd_5195026] using wordTrace_append hprefix tailTrace_5195026
  have hstable : (prefixWord ++ tailWord_5195026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195026).length < 2 ^ (prefixWord ++ tailWord_5195026).sum := by decide
  have hdescent : baseEnd_5195026 < baseStart_5195026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195045 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 5]
def baseStart_5195045 : Nat := 118140960795 + 5195045 * 2 ^ 59
def prefixEnd_5195045 : Nat := 4983230072969 + 3 ^ 40 * 5195045 * 2
def baseEnd_5195045 : Nat := 296395011859636899582881

theorem tailTrace_5195045 : CollatzResearch.WordTrace tailWord_5195045 prefixEnd_5195045 296395011859636899582881 := by
  unfold tailWord_5195045
  simp only [CollatzResearch.WordTrace]
  refine ⟨189478857464246682894082589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126319238309497788596055059 189478857464246682894082589)
  ·
    refine ⟨71054571549092506085280971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189478857464246682894082589 71054571549092506085280971)
    ·
      refine ⟨106581857323638759127921457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71054571549092506085280971 106581857323638759127921457)
      ·
        refine ⟨79936392992729069345941093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106581857323638759127921457 79936392992729069345941093)
        ·
          refine ⟨14988073686136700502363955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79936392992729069345941093 14988073686136700502363955)
          ·
            refine ⟨22482110529205050753545933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14988073686136700502363955 22482110529205050753545933)
            ·
              refine ⟨8430791448451894032579725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22482110529205050753545933 8430791448451894032579725)
              ·
                refine ⟨3161546793169460262217397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8430791448451894032579725 3161546793169460262217397)
                ·
                  refine ⟨296395011859636899582881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3161546793169460262217397 296395011859636899582881)
                  ·
                    rfl

theorem cell23_5195045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_5195045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195045 prefixEnd_5195045 := by exact prefixLift 5195045
  have htrace : WordTrace (prefixWord ++ tailWord_5195045) baseStart_5195045 baseEnd_5195045 := by
    simpa [prefixWord, tailWord_5195045, baseEnd_5195045] using wordTrace_append hprefix tailTrace_5195045
  have hstable : (prefixWord ++ tailWord_5195045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195045).length < 2 ^ (prefixWord ++ tailWord_5195045).sum := by decide
  have hdescent : baseEnd_5195045 < baseStart_5195045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195058 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_5195058 : Nat := 118140960795 + 5195058 * 2 ^ 59
def prefixEnd_5195058 : Nat := 4983230072969 + 3 ^ 40 * 5195058 * 2
def baseEnd_5195058 : Nat := 889187260661746848461123

theorem tailTrace_5195058 : CollatzResearch.WordTrace tailWord_5195058 prefixEnd_5195058 889187260661746848461123 := by
  unfold tailWord_5195058
  simp only [CollatzResearch.WordTrace]
  refine ⟨47369832903299896528576457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126319554408799724076203885 47369832903299896528576457)
  ·
    refine ⟨35527374677474922396432343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47369832903299896528576457 35527374677474922396432343)
    ·
      refine ⟨53291062016212383594648515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35527374677474922396432343 53291062016212383594648515)
      ·
        refine ⟨79936593024318575391972773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53291062016212383594648515 79936593024318575391972773)
        ·
          refine ⟨14988111192059732885994895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79936593024318575391972773 14988111192059732885994895)
          ·
            refine ⟨22482166788089599328992343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14988111192059732885994895 22482166788089599328992343)
            ·
              refine ⟨33723250182134398993488515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22482166788089599328992343 33723250182134398993488515)
              ·
                refine ⟨50584875273201598490232773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33723250182134398993488515 50584875273201598490232773)
                ·
                  refine ⟨9484664113725299716918645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50584875273201598490232773 9484664113725299716918645)
                  ·
                    refine ⟨889187260661746848461123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9484664113725299716918645 889187260661746848461123)
                    ·
                      rfl

theorem cell23_5195058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_5195058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195058 prefixEnd_5195058 := by exact prefixLift 5195058
  have htrace : WordTrace (prefixWord ++ tailWord_5195058) baseStart_5195058 baseEnd_5195058 := by
    simpa [prefixWord, tailWord_5195058, baseEnd_5195058] using wordTrace_append hprefix tailTrace_5195058
  have hstable : (prefixWord ++ tailWord_5195058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195058).length < 2 ^ (prefixWord ++ tailWord_5195058).sum := by decide
  have hdescent : baseEnd_5195058 < baseStart_5195058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195068 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_5195068 : Nat := 118140960795 + 5195068 * 2 ^ 59
def prefixEnd_5195068 : Nat := 4983230072969 + 3 ^ 40 * 5195068 * 2
def baseEnd_5195068 : Nat := 2667566916791785506258323

theorem tailTrace_5195068 : CollatzResearch.WordTrace tailWord_5195068 prefixEnd_5195068 2667566916791785506258323 := by
  unfold tailWord_5195068
  simp only [CollatzResearch.WordTrace]
  refine ⟨94739848171581678911084929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126319797562108905214779905 94739848171581678911084929)
  ·
    refine ⟨71054886128686259183313697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94739848171581678911084929 71054886128686259183313697)
    ·
      refine ⟨53291164596514694387485273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71054886128686259183313697 53291164596514694387485273)
      ·
        refine ⟨39968373447386020790613955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53291164596514694387485273 39968373447386020790613955)
        ·
          refine ⟨59952560171079031185920933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39968373447386020790613955 59952560171079031185920933)
          ·
            refine ⟨11241105032077318347360175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59952560171079031185920933 11241105032077318347360175)
            ·
              refine ⟨16861657548115977521040263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11241105032077318347360175 16861657548115977521040263)
              ·
                refine ⟨25292486322173966281560395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16861657548115977521040263 25292486322173966281560395)
                ·
                  refine ⟨37938729483260949422340593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25292486322173966281560395 37938729483260949422340593)
                  ·
                    refine ⟨28454047112445712066755445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37938729483260949422340593 28454047112445712066755445)
                    ·
                      refine ⟨2667566916791785506258323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28454047112445712066755445 2667566916791785506258323)
                      ·
                        rfl

theorem cell23_5195068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_5195068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195068 prefixEnd_5195068 := by exact prefixLift 5195068
  have htrace : WordTrace (prefixWord ++ tailWord_5195068) baseStart_5195068 baseEnd_5195068 := by
    simpa [prefixWord, tailWord_5195068, baseEnd_5195068] using wordTrace_append hprefix tailTrace_5195068
  have hstable : (prefixWord ++ tailWord_5195068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195068).length < 2 ^ (prefixWord ++ tailWord_5195068).sum := by decide
  have hdescent : baseEnd_5195068 < baseStart_5195068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195088 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 5, 4]
def baseStart_5195088 : Nat := 118140960795 + 5195088 * 2 ^ 59
def prefixEnd_5195088 : Nat := 4983230072969 + 3 ^ 40 * 5195088 * 2
def baseEnd_5195088 : Nat := 889192395468291809336077

theorem tailTrace_5195088 : CollatzResearch.WordTrace tailWord_5195088 prefixEnd_5195088 889192395468291809336077 := by
  unfold tailWord_5195088
  simp only [CollatzResearch.WordTrace]
  refine ⟨94740212901545450618948959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126320283868727267491931945 94740212901545450618948959)
  ·
    refine ⟨142110319352318175928423439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94740212901545450618948959 142110319352318175928423439)
    ·
      refine ⟨213165479028477263892635159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142110319352318175928423439 213165479028477263892635159)
      ·
        refine ⟨319748218542715895838952739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213165479028477263892635159 319748218542715895838952739)
        ·
          refine ⟨479622327814073843758429109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319748218542715895838952739 479622327814073843758429109)
          ·
            refine ⟨44964593232569422852352729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 479622327814073843758429109 44964593232569422852352729)
            ·
              refine ⟨33723444924427067139264547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44964593232569422852352729 33723444924427067139264547)
              ·
                refine ⟨50585167386640600708896821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33723444924427067139264547 50585167386640600708896821)
                ·
                  refine ⟨4742359442497556316459077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50585167386640600708896821 4742359442497556316459077)
                  ·
                    refine ⟨889192395468291809336077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4742359442497556316459077 889192395468291809336077)
                    ·
                      rfl

theorem cell23_5195088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_5195088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195088 prefixEnd_5195088 := by exact prefixLift 5195088
  have htrace : WordTrace (prefixWord ++ tailWord_5195088) baseStart_5195088 baseEnd_5195088 := by
    simpa [prefixWord, tailWord_5195088, baseEnd_5195088] using wordTrace_append hprefix tailTrace_5195088
  have hstable : (prefixWord ++ tailWord_5195088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195088).length < 2 ^ (prefixWord ++ tailWord_5195088).sum := by decide
  have hdescent : baseEnd_5195088 < baseStart_5195088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195095 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_5195095 : Nat := 118140960795 + 5195095 * 2 ^ 59
def prefixEnd_5195095 : Nat := 4983230072969 + 3 ^ 40 * 5195095 * 2
def baseEnd_5195095 : Nat := 2667580780769456900620699

theorem tailTrace_5195095 : CollatzResearch.WordTrace tailWord_5195095 prefixEnd_5195095 2667580780769456900620699 := by
  unfold tailWord_5195095
  simp only [CollatzResearch.WordTrace]
  refine ⟨189480681114065541433402739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126320454076043694288935159 189480681114065541433402739)
  ·
    refine ⟨284221021671098312150104109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189480681114065541433402739 284221021671098312150104109)
    ·
      refine ⟨106582883126661867056289041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284221021671098312150104109 106582883126661867056289041)
      ·
        refine ⟨79937162344996400292216781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106582883126661867056289041 79937162344996400292216781)
        ·
          refine ⟨29976435879373650109581293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79937162344996400292216781 29976435879373650109581293)
          ·
            refine ⟨11241163454765118791092985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29976435879373650109581293 11241163454765118791092985)
            ·
              refine ⟨8430872591073839093319739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11241163454765118791092985 8430872591073839093319739)
              ·
                refine ⟨12646308886610758639979609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8430872591073839093319739 12646308886610758639979609)
                ·
                  refine ⟨9484731664958068979984707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12646308886610758639979609 9484731664958068979984707)
                  ·
                    refine ⟨14227097497437103469977061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9484731664958068979984707 14227097497437103469977061)
                    ·
                      refine ⟨2667580780769456900620699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14227097497437103469977061 2667580780769456900620699)
                      ·
                        rfl

theorem cell23_5195095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_5195095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195095 prefixEnd_5195095 := by exact prefixLift 5195095
  have htrace : WordTrace (prefixWord ++ tailWord_5195095) baseStart_5195095 baseEnd_5195095 := by
    simpa [prefixWord, tailWord_5195095, baseEnd_5195095] using wordTrace_append hprefix tailTrace_5195095
  have hstable : (prefixWord ++ tailWord_5195095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195095).length < 2 ^ (prefixWord ++ tailWord_5195095).sum := by decide
  have hdescent : baseEnd_5195095 < baseStart_5195095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195098 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_5195098 : Nat := 118140960795 + 5195098 * 2 ^ 59
def prefixEnd_5195098 : Nat := 4983230072969 + 3 ^ 40 * 5195098 * 2
def baseEnd_5195098 : Nat := 2667582321211420388883185

theorem tailTrace_5195098 : CollatzResearch.WordTrace tailWord_5195098 prefixEnd_5195098 2667582321211420388883185 := by
  unfold tailWord_5195098
  simp only [CollatzResearch.WordTrace]
  refine ⟨47370197633263668236440487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126320527022036448630507965 47370197633263668236440487)
  ·
    refine ⟨71055296449895502354660731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47370197633263668236440487 71055296449895502354660731)
    ·
      refine ⟨106582944674843253531991097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71055296449895502354660731 106582944674843253531991097)
      ·
        refine ⟨79937208506132440148993323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106582944674843253531991097 79937208506132440148993323)
        ·
          refine ⟨119905812759198660223489985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79937208506132440148993323 119905812759198660223489985)
          ·
            refine ⟨89929359569398995167617489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119905812759198660223489985 89929359569398995167617489)
            ·
              refine ⟨67447019677049246375713117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89929359569398995167617489 67447019677049246375713117)
              ·
                refine ⟨25292632378893467390892419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67447019677049246375713117 25292632378893467390892419)
                ·
                  refine ⟨37938948568340201086338629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25292632378893467390892419 37938948568340201086338629)
                  ·
                    refine ⟨7113552856563787703688493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37938948568340201086338629 7113552856563787703688493)
                    ·
                      refine ⟨2667582321211420388883185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7113552856563787703688493 2667582321211420388883185)
                      ·
                        rfl

theorem cell23_5195098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_5195098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195098 prefixEnd_5195098 := by exact prefixLift 5195098
  have htrace : WordTrace (prefixWord ++ tailWord_5195098) baseStart_5195098 baseEnd_5195098 := by
    simpa [prefixWord, tailWord_5195098, baseEnd_5195098] using wordTrace_append hprefix tailTrace_5195098
  have hstable : (prefixWord ++ tailWord_5195098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195098).length < 2 ^ (prefixWord ++ tailWord_5195098).sum := by decide
  have hdescent : baseEnd_5195098 < baseStart_5195098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195122 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_5195122 : Nat := 118140960795 + 5195122 * 2 ^ 59
def prefixEnd_5195122 : Nat := 4983230072969 + 3 ^ 40 * 5195122 * 2
def baseEnd_5195122 : Nat := 889198214915709431661025

theorem tailTrace_5195122 : CollatzResearch.WordTrace tailWord_5195122 prefixEnd_5195122 889198214915709431661025 := by
  unfold tailWord_5195122
  simp only [CollatzResearch.WordTrace]
  refine ⟨47370416471241931261158905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126321110589978483363090413 47370416471241931261158905)
  ·
    refine ⟨35527812353431448445869179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47370416471241931261158905 35527812353431448445869179)
    ·
      refine ⟨53291718530147172668803769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35527812353431448445869179 53291718530147172668803769)
      ·
        refine ⟨39968788897610379501602827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53291718530147172668803769 39968788897610379501602827)
        ·
          refine ⟨59953183346415569252404241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39968788897610379501602827 59953183346415569252404241)
          ·
            refine ⟨44964887509811676939303181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59953183346415569252404241 44964887509811676939303181)
            ·
              refine ⟨16861832816179378852238693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44964887509811676939303181 16861832816179378852238693)
              ·
                refine ⟨3161593653033633534794755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16861832816179378852238693 3161593653033633534794755)
                ·
                  refine ⟨4742390479550450302192133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161593653033633534794755 4742390479550450302192133)
                  ·
                    refine ⟨889198214915709431661025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4742390479550450302192133 889198214915709431661025)
                    ·
                      rfl

theorem cell23_5195122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_5195122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195122 prefixEnd_5195122 := by exact prefixLift 5195122
  have htrace : WordTrace (prefixWord ++ tailWord_5195122) baseStart_5195122 baseEnd_5195122 := by
    simpa [prefixWord, tailWord_5195122, baseEnd_5195122] using wordTrace_append hprefix tailTrace_5195122
  have hstable : (prefixWord ++ tailWord_5195122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195122).length < 2 ^ (prefixWord ++ tailWord_5195122).sum := by decide
  have hdescent : baseEnd_5195122 < baseStart_5195122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195148 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_5195148 : Nat := 118140960795 + 5195148 * 2 ^ 59
def prefixEnd_5195148 : Nat := 4983230072969 + 3 ^ 40 * 5195148 * 2
def baseEnd_5195148 : Nat := 889202665081381731085985

theorem tailTrace_5195148 : CollatzResearch.WordTrace tailWord_5195148 prefixEnd_5195148 889202665081381731085985 := by
  unfold tailWord_5195148
  simp only [CollatzResearch.WordTrace]
  refine ⟨94741307091436765742541049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126321742788582354323388065 94741307091436765742541049)
  ·
    refine ⟨71055980318577574306905787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94741307091436765742541049 71055980318577574306905787)
    ·
      refine ⟨106583970477866361460358681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71055980318577574306905787 106583970477866361460358681)
      ·
        refine ⟨79937977858399771095269011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106583970477866361460358681 79937977858399771095269011)
        ·
          refine ⟨119906966787599656642903517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79937977858399771095269011 119906966787599656642903517)
          ·
            refine ⟨44965112545349871241088819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119906966787599656642903517 44965112545349871241088819)
            ·
              refine ⟨67447668818024806861633229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44965112545349871241088819 67447668818024806861633229)
              ·
                refine ⟨25292875806759302573112461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67447668818024806861633229 25292875806759302573112461)
                ·
                  refine ⟨9484828427534738464917173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25292875806759302573112461 9484828427534738464917173)
                  ·
                    refine ⟨889202665081381731085985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9484828427534738464917173 889202665081381731085985)
                    ·
                      rfl

theorem cell23_5195148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_5195148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195148 prefixEnd_5195148 := by exact prefixLift 5195148
  have htrace : WordTrace (prefixWord ++ tailWord_5195148) baseStart_5195148 baseEnd_5195148 := by
    simpa [prefixWord, tailWord_5195148, baseEnd_5195148] using wordTrace_append hprefix tailTrace_5195148
  have hstable : (prefixWord ++ tailWord_5195148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195148).length < 2 ^ (prefixWord ++ tailWord_5195148).sum := by decide
  have hdescent : baseEnd_5195148 < baseStart_5195148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195208 : List Nat := [2, 1, 3, 1, 3, 1, 3, 9]
def baseStart_5195208 : Nat := 118140960795 + 5195208 * 2 ^ 59
def prefixEnd_5195208 : Nat := 4983230072969 + 3 ^ 40 * 5195208 * 2
def baseEnd_5195208 : Nat := 98801437188274628092877

theorem tailTrace_5195208 : CollatzResearch.WordTrace tailWord_5195208 prefixEnd_5195208 98801437188274628092877 := by
  unfold tailWord_5195208
  simp only [CollatzResearch.WordTrace]
  refine ⟨94742401281328080866133139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126323201708437441154844185 94742401281328080866133139)
  ·
    refine ⟨142113601921992121299199709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94742401281328080866133139 142113601921992121299199709)
    ·
      refine ⟨53292600720747045487199891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142113601921992121299199709 53292600720747045487199891)
      ·
        refine ⟨79938901081120568230799837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53292600720747045487199891 79938901081120568230799837)
        ·
          refine ⟨29977087905420213086549939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79938901081120568230799837 29977087905420213086549939)
          ·
            refine ⟨44965631858130319629824909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29977087905420213086549939 44965631858130319629824909)
            ·
              refine ⟨16862111946798869861184341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44965631858130319629824909 16862111946798869861184341)
              ·
                refine ⟨98801437188274628092877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16862111946798869861184341 98801437188274628092877)
                ·
                  rfl

theorem cell23_5195208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 9].length) (baseStart_5195208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195208 prefixEnd_5195208 := by exact prefixLift 5195208
  have htrace : WordTrace (prefixWord ++ tailWord_5195208) baseStart_5195208 baseEnd_5195208 := by
    simpa [prefixWord, tailWord_5195208, baseEnd_5195208] using wordTrace_append hprefix tailTrace_5195208
  have hstable : (prefixWord ++ tailWord_5195208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195208).length < 2 ^ (prefixWord ++ tailWord_5195208).sum := by decide
  have hdescent : baseEnd_5195208 < baseStart_5195208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195222 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5195222 : Nat := 118140960795 + 5195222 * 2 ^ 59
def prefixEnd_5195222 : Nat := 4983230072969 + 3 ^ 40 * 5195222 * 2
def baseEnd_5195222 : Nat := 2667645992812577903732615

theorem tailTrace_5195222 : CollatzResearch.WordTrace tailWord_5195222 prefixEnd_5195222 2667645992812577903732615 := by
  unfold tailWord_5195222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842832074037840132704745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126323542123070294748850613 11842832074037840132704745)
  ·
    refine ⟨8882124055528380099528559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11842832074037840132704745 8882124055528380099528559)
    ·
      refine ⟨13323186083292570149292839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8882124055528380099528559 13323186083292570149292839)
      ·
        refine ⟨19984779124938855223939259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13323186083292570149292839 19984779124938855223939259)
        ·
          refine ⟨29977168687408282835908889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19984779124938855223939259 29977168687408282835908889)
          ·
            refine ⟨22482876515556212126931667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29977168687408282835908889 22482876515556212126931667)
            ·
              refine ⟨33724314773334318190397501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22482876515556212126931667 33724314773334318190397501)
              ·
                refine ⟨12646618040000369321399063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33724314773334318190397501 12646618040000369321399063)
                ·
                  refine ⟨18969927060000553982098595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12646618040000369321399063 18969927060000553982098595)
                  ·
                    refine ⟨28454890590000830973147893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18969927060000553982098595 28454890590000830973147893)
                    ·
                      refine ⟨2667645992812577903732615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28454890590000830973147893 2667645992812577903732615)
                      ·
                        rfl

theorem cell23_5195222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5195222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195222 prefixEnd_5195222 := by exact prefixLift 5195222
  have htrace : WordTrace (prefixWord ++ tailWord_5195222) baseStart_5195222 baseEnd_5195222 := by
    simpa [prefixWord, tailWord_5195222, baseEnd_5195222] using wordTrace_append hprefix tailTrace_5195222
  have hstable : (prefixWord ++ tailWord_5195222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195222).length < 2 ^ (prefixWord ++ tailWord_5195222).sum := by decide
  have hdescent : baseEnd_5195222 < baseStart_5195222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195270 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5195270 : Nat := 118140960795 + 5195270 * 2 ^ 59
def prefixEnd_5195270 : Nat := 4983230072969 + 3 ^ 40 * 5195270 * 2
def baseEnd_5195270 : Nat := 2667670639883993715932395

theorem tailTrace_5195270 : CollatzResearch.WordTrace tailWord_5195270 prefixEnd_5195270 2667670639883993715932395 := by
  unfold tailWord_5195270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921470746513485822531977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126324709258954364214015509 5921470746513485822531977)
  ·
    refine ⟨4441103059885114366898983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5921470746513485822531977 4441103059885114366898983)
    ·
      refine ⟨6661654589827671550348475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4441103059885114366898983 6661654589827671550348475)
      ·
        refine ⟨9992481884741507325522713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6661654589827671550348475 9992481884741507325522713)
        ·
          refine ⟨7494361413556130494142035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9992481884741507325522713 7494361413556130494142035)
          ·
            refine ⟨11241542120334195741213053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494361413556130494142035 11241542120334195741213053)
            ·
              refine ⟨4215578295125323402954895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11241542120334195741213053 4215578295125323402954895)
              ·
                refine ⟨6323367442687985104432343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4215578295125323402954895 6323367442687985104432343)
                ·
                  refine ⟨9485051164031977656648515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6323367442687985104432343 9485051164031977656648515)
                  ·
                    refine ⟨14227576746047966484972773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9485051164031977656648515 14227576746047966484972773)
                    ·
                      refine ⟨2667670639883993715932395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14227576746047966484972773 2667670639883993715932395)
                      ·
                        rfl

theorem cell23_5195270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5195270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195270 prefixEnd_5195270 := by exact prefixLift 5195270
  have htrace : WordTrace (prefixWord ++ tailWord_5195270) baseStart_5195270 baseEnd_5195270 := by
    simpa [prefixWord, tailWord_5195270, baseEnd_5195270] using wordTrace_append hprefix tailTrace_5195270
  have hstable : (prefixWord ++ tailWord_5195270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195270).length < 2 ^ (prefixWord ++ tailWord_5195270).sum := by decide
  have hdescent : baseEnd_5195270 < baseStart_5195270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195292 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_5195292 : Nat := 118140960795 + 5195292 * 2 ^ 59
def prefixEnd_5195292 : Nat := 4983230072969 + 3 ^ 40 * 5195292 * 2
def baseEnd_5195292 : Nat := 2667681936458392629857293

theorem tailTrace_5195292 : CollatzResearch.WordTrace tailWord_5195292 prefixEnd_5195292 2667681936458392629857293 := by
  unfold tailWord_5195292
  simp only [CollatzResearch.WordTrace]
  refine ⟨94743933147175922039162065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126325244196234562718882753 94743933147175922039162065)
  ·
    refine ⟨71057949860381941529371549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94743933147175922039162065 71057949860381941529371549)
    ·
      refine ⟨26646731197643228073514331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71057949860381941529371549 26646731197643228073514331)
      ·
        refine ⟨39970096796464842110271497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26646731197643228073514331 39970096796464842110271497)
        ·
          refine ⟨29977572597348631582703623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39970096796464842110271497 29977572597348631582703623)
          ·
            refine ⟨44966358896022947374055435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29977572597348631582703623 44966358896022947374055435)
            ·
              refine ⟨67449538344034421061083153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44966358896022947374055435 67449538344034421061083153)
              ·
                refine ⟨50587153758025815795812365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67449538344034421061083153 50587153758025815795812365)
                ·
                  refine ⟨18970182659259680923429637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50587153758025815795812365 18970182659259680923429637)
                  ·
                    refine ⟨3556909248611190173143057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18970182659259680923429637 3556909248611190173143057)
                    ·
                      refine ⟨2667681936458392629857293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3556909248611190173143057 2667681936458392629857293)
                      ·
                        rfl

theorem cell23_5195292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_5195292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195292 prefixEnd_5195292 := by exact prefixLift 5195292
  have htrace : WordTrace (prefixWord ++ tailWord_5195292) baseStart_5195292 baseEnd_5195292 := by
    simpa [prefixWord, tailWord_5195292, baseEnd_5195292] using wordTrace_append hprefix tailTrace_5195292
  have hstable : (prefixWord ++ tailWord_5195292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195292).length < 2 ^ (prefixWord ++ tailWord_5195292).sum := by decide
  have hdescent : baseEnd_5195292 < baseStart_5195292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195295 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_5195295 : Nat := 118140960795 + 5195295 * 2 ^ 59
def prefixEnd_5195295 : Nat := 4983230072969 + 3 ^ 40 * 5195295 * 2
def baseEnd_5195295 : Nat := 2667683476900356118119779

theorem tailTrace_5195295 : CollatzResearch.WordTrace tailWord_5195295 prefixEnd_5195295 2667683476900356118119779 := by
  unfold tailWord_5195295
  simp only [CollatzResearch.WordTrace]
  refine ⟨189487975713340975590683339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126325317142227317060455559 189487975713340975590683339)
  ·
    refine ⟨284231963570011463386025009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189487975713340975590683339 284231963570011463386025009)
    ·
      refine ⟨213173972677508597539518757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284231963570011463386025009 213173972677508597539518757)
      ·
        refine ⟨39970119877032862038659767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 213173972677508597539518757 39970119877032862038659767)
        ·
          refine ⟨59955179815549293057989651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39970119877032862038659767 59955179815549293057989651)
          ·
            refine ⟨89932769723323939586984477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59955179815549293057989651 89932769723323939586984477)
            ·
              refine ⟨33724788646246477345119179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89932769723323939586984477 33724788646246477345119179)
              ·
                refine ⟨50587182969369716017678769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33724788646246477345119179 50587182969369716017678769)
                ·
                  refine ⟨37940387227027287013259077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50587182969369716017678769 37940387227027287013259077)
                  ·
                    refine ⟨7113822605067616314986077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37940387227027287013259077 7113822605067616314986077)
                    ·
                      refine ⟨2667683476900356118119779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7113822605067616314986077 2667683476900356118119779)
                      ·
                        rfl

theorem cell23_5195295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_5195295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195295 prefixEnd_5195295 := by exact prefixLift 5195295
  have htrace : WordTrace (prefixWord ++ tailWord_5195295) baseStart_5195295 baseEnd_5195295 := by
    simpa [prefixWord, tailWord_5195295, baseEnd_5195295] using wordTrace_append hprefix tailTrace_5195295
  have hstable : (prefixWord ++ tailWord_5195295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195295).length < 2 ^ (prefixWord ++ tailWord_5195295).sum := by decide
  have hdescent : baseEnd_5195295 < baseStart_5195295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195315 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 7]
def baseStart_5195315 : Nat := 118140960795 + 5195315 * 2 ^ 59
def prefixEnd_5195315 : Nat := 4983230072969 + 3 ^ 40 * 5195315 * 2
def baseEnd_5195315 : Nat := 296410416279271782207743

theorem tailTrace_5195315 : CollatzResearch.WordTrace tailWord_5195315 prefixEnd_5195315 296410416279271782207743 := by
  unfold tailWord_5195315
  simp only [CollatzResearch.WordTrace]
  refine ⟨189488705173268519006411399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126325803448845679337607599 189488705173268519006411399)
  ·
    refine ⟨284233057759902778509617099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189488705173268519006411399 284233057759902778509617099)
    ·
      refine ⟨426349586639854167764425649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284233057759902778509617099 426349586639854167764425649)
      ·
        refine ⟨319762189979890625823319237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426349586639854167764425649 319762189979890625823319237)
        ·
          refine ⟨59955410621229492341872357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319762189979890625823319237 59955410621229492341872357)
          ·
            refine ⟨11241639491480529814101067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59955410621229492341872357 11241639491480529814101067)
            ·
              refine ⟨16862459237220794721151601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11241639491480529814101067 16862459237220794721151601)
              ·
                refine ⟨12646844427915596040863701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16862459237220794721151601 12646844427915596040863701)
                ·
                  refine ⟨296410416279271782207743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12646844427915596040863701 296410416279271782207743)
                  ·
                    rfl

theorem cell23_5195315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 7].length) (baseStart_5195315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195315 prefixEnd_5195315 := by exact prefixLift 5195315
  have htrace : WordTrace (prefixWord ++ tailWord_5195315) baseStart_5195315 baseEnd_5195315 := by
    simpa [prefixWord, tailWord_5195315, baseEnd_5195315] using wordTrace_append hprefix tailTrace_5195315
  have hstable : (prefixWord ++ tailWord_5195315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195315).length < 2 ^ (prefixWord ++ tailWord_5195315).sum := by decide
  have hdescent : baseEnd_5195315 < baseStart_5195315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195345 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_5195345 : Nat := 118140960795 + 5195345 * 2 ^ 59
def prefixEnd_5195345 : Nat := 4983230072969 + 3 ^ 40 * 5195345 * 2
def baseEnd_5195345 : Nat := 889236383644360307498183

theorem tailTrace_5195345 : CollatzResearch.WordTrace tailWord_5195345 prefixEnd_5195345 889236383644360307498183 := by
  unfold tailWord_5195345
  simp only [CollatzResearch.WordTrace]
  refine ⟨189489799363159834130003489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126326532908773222753335659 189489799363159834130003489)
  ·
    refine ⟨142117349522369875597502617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189489799363159834130003489 142117349522369875597502617)
    ·
      refine ⟨106588012141777406698126963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142117349522369875597502617 106588012141777406698126963)
      ·
        refine ⟨159882018212666110047190445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106588012141777406698126963 159882018212666110047190445)
        ·
          refine ⟨59955756829749791267696417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159882018212666110047190445 59955756829749791267696417)
          ·
            refine ⟨44966817622312343450772313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59955756829749791267696417 44966817622312343450772313)
            ·
              refine ⟨33725113216734257588079235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44966817622312343450772313 33725113216734257588079235)
              ·
                refine ⟨50587669825101386382118853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33725113216734257588079235 50587669825101386382118853)
                ·
                  refine ⟨9485188092206509946647285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50587669825101386382118853 9485188092206509946647285)
                  ·
                    refine ⟨889236383644360307498183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9485188092206509946647285 889236383644360307498183)
                    ·
                      rfl

theorem cell23_5195345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_5195345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195345 prefixEnd_5195345 := by exact prefixLift 5195345
  have htrace : WordTrace (prefixWord ++ tailWord_5195345) baseStart_5195345 baseEnd_5195345 := by
    simpa [prefixWord, tailWord_5195345, baseEnd_5195345] using wordTrace_append hprefix tailTrace_5195345
  have hstable : (prefixWord ++ tailWord_5195345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195345).length < 2 ^ (prefixWord ++ tailWord_5195345).sum := by decide
  have hdescent : baseEnd_5195345 < baseStart_5195345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195482 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_5195482 : Nat := 118140960795 + 5195482 * 2 ^ 59
def prefixEnd_5195482 : Nat := 4983230072969 + 3 ^ 40 * 5195482 * 2
def baseEnd_5195482 : Nat := 889259832594248962160473

theorem tailTrace_5195482 : CollatzResearch.WordTrace tailWord_5195482 prefixEnd_5195482 889259832594248962160473 := by
  unfold tailWord_5195482
  simp only [CollatzResearch.WordTrace]
  refine ⟨47373699040915876631935175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126329864109109004351827133 47373699040915876631935175)
  ·
    refine ⟨71060548561373814947902763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47373699040915876631935175 71060548561373814947902763)
    ·
      refine ⟨106590822842060722421854145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71060548561373814947902763 106590822842060722421854145)
      ·
        refine ⟨79943117131545541816390609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106590822842060722421854145 79943117131545541816390609)
        ·
          refine ⟨59957337848659156362292957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79943117131545541816390609 59957337848659156362292957)
          ·
            refine ⟨22484001693247183635859859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59957337848659156362292957 22484001693247183635859859)
            ·
              refine ⟨33726002539870775453789789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22484001693247183635859859 33726002539870775453789789)
              ·
                refine ⟨12647250952451540795171171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33726002539870775453789789 12647250952451540795171171)
                ·
                  refine ⟨18970876428677311192756757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12647250952451540795171171 18970876428677311192756757)
                  ·
                    refine ⟨889259832594248962160473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18970876428677311192756757 889259832594248962160473)
                    ·
                      rfl

theorem cell23_5195482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_5195482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195482 prefixEnd_5195482 := by exact prefixLift 5195482
  have htrace : WordTrace (prefixWord ++ tailWord_5195482) baseStart_5195482 baseEnd_5195482 := by
    simpa [prefixWord, tailWord_5195482, baseEnd_5195482] using wordTrace_append hprefix tailTrace_5195482
  have hstable : (prefixWord ++ tailWord_5195482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195482).length < 2 ^ (prefixWord ++ tailWord_5195482).sum := by decide
  have hdescent : baseEnd_5195482 < baseStart_5195482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195506 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5195506 : Nat := 118140960795 + 5195506 * 2 ^ 59
def prefixEnd_5195506 : Nat := 4983230072969 + 3 ^ 40 * 5195506 * 2
def baseEnd_5195506 : Nat := 2667791821318454792581309

theorem tailTrace_5195506 : CollatzResearch.WordTrace tailWord_5195506 prefixEnd_5195506 2667791821318454792581309 := by
  unfold tailWord_5195506
  simp only [CollatzResearch.WordTrace]
  refine ⟨47373917878894139656653593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126330447677051039084409581 47373917878894139656653593)
  ·
    refine ⟨35530438409170604742490195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47373917878894139656653593 35530438409170604742490195)
    ·
      refine ⟨53295657613755907113735293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35530438409170604742490195 53295657613755907113735293)
      ·
        refine ⟨19985871605158465167650735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53295657613755907113735293 19985871605158465167650735)
        ·
          refine ⟨29978807407737697751476103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19985871605158465167650735 29978807407737697751476103)
          ·
            refine ⟨44968211111606546627214155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29978807407737697751476103 44968211111606546627214155)
            ·
              refine ⟨67452316667409819940821233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44968211111606546627214155 67452316667409819940821233)
              ·
                refine ⟨50589237500557364955615925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67452316667409819940821233 50589237500557364955615925)
                ·
                  refine ⟨4742741015677252964588993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50589237500557364955615925 4742741015677252964588993)
                  ·
                    refine ⟨3557055761757939723441745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4742741015677252964588993 3557055761757939723441745)
                    ·
                      refine ⟨2667791821318454792581309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557055761757939723441745 2667791821318454792581309)
                      ·
                        rfl

theorem cell23_5195506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5195506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195506 prefixEnd_5195506 := by exact prefixLift 5195506
  have htrace : WordTrace (prefixWord ++ tailWord_5195506) baseStart_5195506 baseEnd_5195506 := by
    simpa [prefixWord, tailWord_5195506, baseEnd_5195506] using wordTrace_append hprefix tailTrace_5195506
  have hstable : (prefixWord ++ tailWord_5195506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195506).length < 2 ^ (prefixWord ++ tailWord_5195506).sum := by decide
  have hdescent : baseEnd_5195506 < baseStart_5195506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195523 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 1, 2, 2]
def baseStart_5195523 : Nat := 118140960795 + 5195523 * 2 ^ 59
def prefixEnd_5195523 : Nat := 4983230072969 + 3 ^ 40 * 5195523 * 2
def baseEnd_5195523 : Nat := 2667800550489581226068731

theorem tailTrace_5195523 : CollatzResearch.WordTrace tailWord_5195523 prefixEnd_5195523 2667800550489581226068731 := by
  unfold tailWord_5195523
  simp only [CollatzResearch.WordTrace]
  refine ⟨189496291556514970529983223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126330861037676647019988815 189496291556514970529983223)
  ·
    refine ⟨284244437334772455794974835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189496291556514970529983223 284244437334772455794974835)
    ·
      refine ⟨426366656002158683692462253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284244437334772455794974835 426366656002158683692462253)
      ·
        refine ⟨159887496000809506384673345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426366656002158683692462253 159887496000809506384673345)
        ·
          refine ⟨119915622000607129788505009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159887496000809506384673345 119915622000607129788505009)
          ·
            refine ⟨89936716500455347341378757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119915622000607129788505009 89936716500455347341378757)
            ·
              refine ⟨16863134343835377626508517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89936716500455347341378757 16863134343835377626508517)
              ·
                refine ⟨3161837689469133304970347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16863134343835377626508517 3161837689469133304970347)
                ·
                  refine ⟨4742756534203699957455521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161837689469133304970347 4742756534203699957455521)
                  ·
                    refine ⟨3557067400652774968091641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4742756534203699957455521 3557067400652774968091641)
                    ·
                      refine ⟨2667800550489581226068731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557067400652774968091641 2667800550489581226068731)
                      ·
                        rfl

theorem cell23_5195523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_5195523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195523 prefixEnd_5195523 := by exact prefixLift 5195523
  have htrace : WordTrace (prefixWord ++ tailWord_5195523) baseStart_5195523 baseEnd_5195523 := by
    simpa [prefixWord, tailWord_5195523, baseEnd_5195523] using wordTrace_append hprefix tailTrace_5195523
  have hstable : (prefixWord ++ tailWord_5195523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195523).length < 2 ^ (prefixWord ++ tailWord_5195523).sum := by decide
  have hdescent : baseEnd_5195523 < baseStart_5195523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195552 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5195552 : Nat := 118140960795 + 5195552 * 2 ^ 59
def prefixEnd_5195552 : Nat := 4983230072969 + 3 ^ 40 * 5195552 * 2
def baseEnd_5195552 : Nat := 2667815441428561612606097

theorem tailTrace_5195552 : CollatzResearch.WordTrace tailWord_5195552 prefixEnd_5195552 2667815441428561612606097 := by
  unfold tailWord_5195552
  simp only [CollatzResearch.WordTrace]
  refine ⟨94748674636704954241394455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126331566182273272321859273 94748674636704954241394455)
  ·
    refine ⟨142123011955057431362091683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94748674636704954241394455 142123011955057431362091683)
    ·
      refine ⟨213184517932586147043137525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142123011955057431362091683 213184517932586147043137525)
      ·
        refine ⟨19986048556179951285294143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213184517932586147043137525 19986048556179951285294143)
        ·
          refine ⟨29979072834269926927941215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19986048556179951285294143 29979072834269926927941215)
          ·
            refine ⟨44968609251404890391911823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29979072834269926927941215 44968609251404890391911823)
            ·
              refine ⟨67452913877107335587867735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44968609251404890391911823 67452913877107335587867735)
              ·
                refine ⟨101179370815661003381801603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67452913877107335587867735 101179370815661003381801603)
                ·
                  refine ⟨151769056223491505072702405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101179370815661003381801603 151769056223491505072702405)
                  ·
                    refine ⟨28456698041904657201131701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151769056223491505072702405 28456698041904657201131701)
                    ·
                      refine ⟨2667815441428561612606097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28456698041904657201131701 2667815441428561612606097)
                      ·
                        rfl

theorem cell23_5195552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5195552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195552 prefixEnd_5195552 := by exact prefixLift 5195552
  have htrace : WordTrace (prefixWord ++ tailWord_5195552) baseStart_5195552 baseEnd_5195552 := by
    simpa [prefixWord, tailWord_5195552, baseEnd_5195552] using wordTrace_append hprefix tailTrace_5195552
  have hstable : (prefixWord ++ tailWord_5195552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195552).length < 2 ^ (prefixWord ++ tailWord_5195552).sum := by decide
  have hdescent : baseEnd_5195552 < baseStart_5195552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195556 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_5195556 : Nat := 118140960795 + 5195556 * 2 ^ 59
def prefixEnd_5195556 : Nat := 4983230072969 + 3 ^ 40 * 5195556 * 2
def baseEnd_5195556 : Nat := 2667817495351179596956079

theorem tailTrace_5195556 : CollatzResearch.WordTrace tailWord_5195556 prefixEnd_5195556 2667817495351179596956079 := by
  unfold tailWord_5195556
  simp only [CollatzResearch.WordTrace]
  refine ⟨94748747582697708582967261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126331663443596944777289681 94748747582697708582967261)
  ·
    refine ⟨35530780343511640718612723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94748747582697708582967261 35530780343511640718612723)
    ·
      refine ⟨53296170515267461077919085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35530780343511640718612723 53296170515267461077919085)
      ·
        refine ⟨19986063943225297904219657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53296170515267461077919085 19986063943225297904219657)
        ·
          refine ⟨14989547957418973428164743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19986063943225297904219657 14989547957418973428164743)
          ·
            refine ⟨22484321936128460142247115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14989547957418973428164743 22484321936128460142247115)
            ·
              refine ⟨33726482904192690213370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22484321936128460142247115 33726482904192690213370673)
              ·
                refine ⟨25294862178144517660028005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33726482904192690213370673 25294862178144517660028005)
                ·
                  refine ⟨4742786658402097061255251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25294862178144517660028005 4742786658402097061255251)
                  ·
                    refine ⟨7114179987603145591882877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4742786658402097061255251 7114179987603145591882877)
                    ·
                      refine ⟨2667817495351179596956079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7114179987603145591882877 2667817495351179596956079)
                      ·
                        rfl

theorem cell23_5195556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_5195556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195556 prefixEnd_5195556 := by exact prefixLift 5195556
  have htrace : WordTrace (prefixWord ++ tailWord_5195556) baseStart_5195556 baseEnd_5195556 := by
    simpa [prefixWord, tailWord_5195556, baseEnd_5195556] using wordTrace_append hprefix tailTrace_5195556
  have hstable : (prefixWord ++ tailWord_5195556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195556).length < 2 ^ (prefixWord ++ tailWord_5195556).sum := by decide
  have hdescent : baseEnd_5195556 < baseStart_5195556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195574 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5195574 : Nat := 118140960795 + 5195574 * 2 ^ 59
def prefixEnd_5195574 : Nat := 4983230072969 + 3 ^ 40 * 5195574 * 2
def baseEnd_5195574 : Nat := 2667826738002960526530997

theorem tailTrace_5195574 : CollatzResearch.WordTrace tailWord_5195574 prefixEnd_5195574 2667826738002960526530997 := by
  unfold tailWord_5195574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11843634479958137890005611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126332101119553470826726517 11843634479958137890005611)
  ·
    refine ⟨17765451719937206835008417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11843634479958137890005611 17765451719937206835008417)
    ·
      refine ⟨13324088789952905126256313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17765451719937206835008417 13324088789952905126256313)
      ·
        refine ⟨9993066592464678844692235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13324088789952905126256313 9993066592464678844692235)
        ·
          refine ⟨14989599888697018267038353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9993066592464678844692235 14989599888697018267038353)
          ·
            refine ⟨11242199916522763700278765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14989599888697018267038353 11242199916522763700278765)
            ·
              refine ⟨4215824968696036387604537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11242199916522763700278765 4215824968696036387604537)
              ·
                refine ⟨3161868726522027290703403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4215824968696036387604537 3161868726522027290703403)
                ·
                  refine ⟨4742803089783040936055105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161868726522027290703403 4742803089783040936055105)
                  ·
                    refine ⟨3557102317337280702041329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4742803089783040936055105 3557102317337280702041329)
                    ·
                      refine ⟨2667826738002960526530997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557102317337280702041329 2667826738002960526530997)
                      ·
                        rfl

theorem cell23_5195574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5195574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195574 prefixEnd_5195574 := by exact prefixLift 5195574
  have htrace : WordTrace (prefixWord ++ tailWord_5195574) baseStart_5195574 baseEnd_5195574 := by
    simpa [prefixWord, tailWord_5195574, baseEnd_5195574] using wordTrace_append hprefix tailTrace_5195574
  have hstable : (prefixWord ++ tailWord_5195574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195574).length < 2 ^ (prefixWord ++ tailWord_5195574).sum := by decide
  have hdescent : baseEnd_5195574 < baseStart_5195574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195630 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_5195630 : Nat := 118140960795 + 5195630 * 2 ^ 59
def prefixEnd_5195630 : Nat := 4983230072969 + 3 ^ 40 * 5195630 * 2
def baseEnd_5195630 : Nat := 2667855492919612307430739

theorem tailTrace_5195630 : CollatzResearch.WordTrace tailWord_5195630 prefixEnd_5195630 2667855492919612307430739 := by
  unfold tailWord_5195630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23687524270890915975516043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126333462778084885202752229 23687524270890915975516043)
  ·
    refine ⟨35531286406336373963274065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23687524270890915975516043 35531286406336373963274065)
    ·
      refine ⟨26648464804752280472455549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35531286406336373963274065 26648464804752280472455549)
      ·
        refine ⟨9993174301782105177170831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26648464804752280472455549 9993174301782105177170831)
        ·
          refine ⟨14989761452673157765756247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9993174301782105177170831 14989761452673157765756247)
          ·
            refine ⟨22484642179009736648634371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14989761452673157765756247 22484642179009736648634371)
            ·
              refine ⟨33726963268514604972951557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22484642179009736648634371 33726963268514604972951557)
              ·
                refine ⟨6323805612846488432428417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33726963268514604972951557 6323805612846488432428417)
                ·
                  refine ⟨4742854209634866324321313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6323805612846488432428417 4742854209634866324321313)
                  ·
                    refine ⟨3557140657226149743240985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4742854209634866324321313 3557140657226149743240985)
                    ·
                      refine ⟨2667855492919612307430739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557140657226149743240985 2667855492919612307430739)
                      ·
                        rfl

theorem cell23_5195630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_5195630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195630 prefixEnd_5195630 := by exact prefixLift 5195630
  have htrace : WordTrace (prefixWord ++ tailWord_5195630) baseStart_5195630 baseEnd_5195630 := by
    simpa [prefixWord, tailWord_5195630, baseEnd_5195630] using wordTrace_append hprefix tailTrace_5195630
  have hstable : (prefixWord ++ tailWord_5195630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195630).length < 2 ^ (prefixWord ++ tailWord_5195630).sum := by decide
  have hdescent : baseEnd_5195630 < baseStart_5195630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195632 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_5195632 : Nat := 118140960795 + 5195632 * 2 ^ 59
def prefixEnd_5195632 : Nat := 4983230072969 + 3 ^ 40 * 5195632 * 2
def baseEnd_5195632 : Nat := 889285506626973766535243

theorem tailTrace_5195632 : CollatzResearch.WordTrace tailWord_5195632 prefixEnd_5195632 889285506626973766535243 := by
  unfold tailWord_5195632
  simp only [CollatzResearch.WordTrace]
  refine ⟨94750133556560041072850575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126333511408746721430467433 94750133556560041072850575)
  ·
    refine ⟨142125200334840061609275863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94750133556560041072850575 142125200334840061609275863)
    ·
      refine ⟨213187800502260092413913795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142125200334840061609275863 213187800502260092413913795)
      ·
        refine ⟨319781700753390138620870693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213187800502260092413913795 319781700753390138620870693)
        ·
          refine ⟨59959068891260650991413255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319781700753390138620870693 59959068891260650991413255)
          ·
            refine ⟨89938603336890976487119883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59959068891260650991413255 89938603336890976487119883)
            ·
              refine ⟨134907905005336464730679825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89938603336890976487119883 134907905005336464730679825)
              ·
                refine ⟨101180928754002348548009869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134907905005336464730679825 101180928754002348548009869)
                ·
                  refine ⟨37942848282750880705503701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101180928754002348548009869 37942848282750880705503701)
                  ·
                    refine ⟨889285506626973766535243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37942848282750880705503701 889285506626973766535243)
                    ·
                      rfl

theorem cell23_5195632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_5195632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195632 prefixEnd_5195632 := by exact prefixLift 5195632
  have htrace : WordTrace (prefixWord ++ tailWord_5195632) baseStart_5195632 baseEnd_5195632 := by
    simpa [prefixWord, tailWord_5195632, baseEnd_5195632] using wordTrace_append hprefix tailTrace_5195632
  have hstable : (prefixWord ++ tailWord_5195632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195632).length < 2 ^ (prefixWord ++ tailWord_5195632).sum := by decide
  have hdescent : baseEnd_5195632 < baseStart_5195632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195666 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_5195666 : Nat := 118140960795 + 5195666 * 2 ^ 59
def prefixEnd_5195666 : Nat := 4983230072969 + 3 ^ 40 * 5195666 * 2
def baseEnd_5195666 : Nat := 889291326074391388860191

theorem tailTrace_5195666 : CollatzResearch.WordTrace tailWord_5195666 prefixEnd_5195666 889291326074391388860191 := by
  unfold tailWord_5195666
  simp only [CollatzResearch.WordTrace]
  refine ⟨47375376798749226488109713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126334338129997937301625901 47375376798749226488109713)
  ·
    refine ⟨35531532599061919866082285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47375376798749226488109713 35531532599061919866082285)
    ·
      refine ⟨13324324724648219949780857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35531532599061919866082285 13324324724648219949780857)
      ·
        refine ⟨9993243543486164962335643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13324324724648219949780857 9993243543486164962335643)
        ·
          refine ⟨14989865315229247443503465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9993243543486164962335643 14989865315229247443503465)
          ·
            refine ⟨11242398986421935582627599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14989865315229247443503465 11242398986421935582627599)
            ·
              refine ⟨16863598479632903373941399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11242398986421935582627599 16863598479632903373941399)
              ·
                refine ⟨25295397719449355060912099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16863598479632903373941399 25295397719449355060912099)
                ·
                  refine ⟨37943096579174032591368149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25295397719449355060912099 37943096579174032591368149)
                  ·
                    refine ⟨889291326074391388860191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37943096579174032591368149 889291326074391388860191)
                    ·
                      rfl

theorem cell23_5195666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_5195666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195666 prefixEnd_5195666 := by exact prefixLift 5195666
  have htrace : WordTrace (prefixWord ++ tailWord_5195666) baseStart_5195666 baseEnd_5195666 := by
    simpa [prefixWord, tailWord_5195666, baseEnd_5195666] using wordTrace_append hprefix tailTrace_5195666
  have hstable : (prefixWord ++ tailWord_5195666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195666).length < 2 ^ (prefixWord ++ tailWord_5195666).sum := by decide
  have hdescent : baseEnd_5195666 < baseStart_5195666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195669 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_5195669 : Nat := 118140960795 + 5195669 * 2 ^ 59
def prefixEnd_5195669 : Nat := 4983230072969 + 3 ^ 40 * 5195669 * 2
def baseEnd_5195669 : Nat := 2667875518665137654843059

theorem tailTrace_5195669 : CollatzResearch.WordTrace tailWord_5195669 prefixEnd_5195669 2667875518665137654843059 := by
  unfold tailWord_5195669
  simp only [CollatzResearch.WordTrace]
  refine ⟨189501616613986037464798061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126334411075990691643198707 189501616613986037464798061)
  ·
    refine ⟨71063106230244764049299273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189501616613986037464798061 71063106230244764049299273)
    ·
      refine ⟨53297329672683573036974455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71063106230244764049299273 53297329672683573036974455)
      ·
        refine ⟨79945994509025359555461683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53297329672683573036974455 79945994509025359555461683)
        ·
          refine ⟨119918991763538039333192525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79945994509025359555461683 119918991763538039333192525)
          ·
            refine ⟨44969621911326764749947197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119918991763538039333192525 44969621911326764749947197)
            ·
              refine ⟨16863608216747536781230199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44969621911326764749947197 16863608216747536781230199)
              ·
                refine ⟨25295412325121305171845299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16863608216747536781230199 25295412325121305171845299)
                ·
                  refine ⟨37943118487681957757767949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25295412325121305171845299 37943118487681957757767949)
                  ·
                    refine ⟨14228669432880734159162981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37943118487681957757767949 14228669432880734159162981)
                    ·
                      refine ⟨2667875518665137654843059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14228669432880734159162981 2667875518665137654843059)
                      ·
                        rfl

theorem cell23_5195669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_5195669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195669 prefixEnd_5195669 := by exact prefixLift 5195669
  have htrace : WordTrace (prefixWord ++ tailWord_5195669) baseStart_5195669 baseEnd_5195669 := by
    simpa [prefixWord, tailWord_5195669, baseEnd_5195669] using wordTrace_append hprefix tailTrace_5195669
  have hstable : (prefixWord ++ tailWord_5195669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195669).length < 2 ^ (prefixWord ++ tailWord_5195669).sum := by decide
  have hdescent : baseEnd_5195669 < baseStart_5195669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195719 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_5195719 : Nat := 118140960795 + 5195719 * 2 ^ 59
def prefixEnd_5195719 : Nat := 4983230072969 + 3 ^ 40 * 5195719 * 2
def baseEnd_5195719 : Nat := 2667901192697862459217829

theorem tailTrace_5195719 : CollatzResearch.WordTrace tailWord_5195719 prefixEnd_5195719 2667901192697862459217829 := by
  unfold tailWord_5195719
  simp only [CollatzResearch.WordTrace]
  refine ⟨189503440263804896004118211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126335626842536597336078807 189503440263804896004118211)
  ·
    refine ⟨284255160395707344006177317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189503440263804896004118211 284255160395707344006177317)
    ·
      refine ⟨53297842574195127001158247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284255160395707344006177317 53297842574195127001158247)
      ·
        refine ⟨79946763861292690501737371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53297842574195127001158247 79946763861292690501737371)
        ·
          refine ⟨119920145791939035752606057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79946763861292690501737371 119920145791939035752606057)
          ·
            refine ⟨89940109343954276814454543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119920145791939035752606057 89940109343954276814454543)
            ·
              refine ⟨134910164015931415221681815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89940109343954276814454543 134910164015931415221681815)
              ·
                refine ⟨202365246023897122832522723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134910164015931415221681815 202365246023897122832522723)
                ·
                  refine ⟨303547869035845684248784085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202365246023897122832522723 303547869035845684248784085)
                  ·
                    refine ⟨7114403180527633224580877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 303547869035845684248784085 7114403180527633224580877)
                    ·
                      refine ⟨2667901192697862459217829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7114403180527633224580877 2667901192697862459217829)
                      ·
                        rfl

theorem cell23_5195719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_5195719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195719 prefixEnd_5195719 := by exact prefixLift 5195719
  have htrace : WordTrace (prefixWord ++ tailWord_5195719) baseStart_5195719 baseEnd_5195719 := by
    simpa [prefixWord, tailWord_5195719, baseEnd_5195719] using wordTrace_append hprefix tailTrace_5195719
  have hstable : (prefixWord ++ tailWord_5195719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195719).length < 2 ^ (prefixWord ++ tailWord_5195719).sum := by decide
  have hdescent : baseEnd_5195719 < baseStart_5195719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195776 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4]
def baseStart_5195776 : Nat := 118140960795 + 5195776 * 2 ^ 59
def prefixEnd_5195776 : Nat := 4983230072969 + 3 ^ 40 * 5195776 * 2
def baseEnd_5195776 : Nat := 2667930461095168736205067

theorem tailTrace_5195776 : CollatzResearch.WordTrace tailWord_5195776 prefixEnd_5195776 2667930461095168736205067 := by
  unfold tailWord_5195776
  simp only [CollatzResearch.WordTrace]
  refine ⟨94752759612299197369471591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126337012816398929825962121 94752759612299197369471591)
  ·
    refine ⟨142129139418448796054207387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94752759612299197369471591 142129139418448796054207387)
    ·
      refine ⟨213193709127673194081311081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142129139418448796054207387 213193709127673194081311081)
      ·
        refine ⟨159895281845754895560983311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213193709127673194081311081 159895281845754895560983311)
        ·
          refine ⟨239842922768632343341474967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159895281845754895560983311 239842922768632343341474967)
          ·
            refine ⟨359764384152948515012212451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239842922768632343341474967 359764384152948515012212451)
            ·
              refine ⟨539646576229422772518318677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359764384152948515012212451 539646576229422772518318677)
              ·
                refine ⟨6323983315188548115449047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 539646576229422772518318677 6323983315188548115449047)
                ·
                  refine ⟨9485974972782822173173571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6323983315188548115449047 9485974972782822173173571)
                  ·
                    refine ⟨14228962459174233259760357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9485974972782822173173571 14228962459174233259760357)
                    ·
                      refine ⟨2667930461095168736205067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14228962459174233259760357 2667930461095168736205067)
                      ·
                        rfl

theorem cell23_5195776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_5195776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195776 prefixEnd_5195776 := by exact prefixLift 5195776
  have htrace : WordTrace (prefixWord ++ tailWord_5195776) baseStart_5195776 baseEnd_5195776 := by
    simpa [prefixWord, tailWord_5195776, baseEnd_5195776] using wordTrace_append hprefix tailTrace_5195776
  have hstable : (prefixWord ++ tailWord_5195776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195776).length < 2 ^ (prefixWord ++ tailWord_5195776).sum := by decide
  have hdescent : baseEnd_5195776 < baseStart_5195776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195779 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5]
def baseStart_5195779 : Nat := 118140960795 + 5195779 * 2 ^ 59
def prefixEnd_5195779 : Nat := 4983230072969 + 3 ^ 40 * 5195779 * 2
def baseEnd_5195779 : Nat := 2667932001537132224467553

theorem tailTrace_5195779 : CollatzResearch.WordTrace tailWord_5195779 prefixEnd_5195779 2667932001537132224467553 := by
  unfold tailWord_5195779
  simp only [CollatzResearch.WordTrace]
  refine ⟨189505628643587526251302391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126337085762391684167534927 189505628643587526251302391)
  ·
    refine ⟨284258442965381289376953587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189505628643587526251302391 284258442965381289376953587)
    ·
      refine ⟨426387664448071934065430381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284258442965381289376953587 426387664448071934065430381)
      ·
        refine ⟨159895374168026975274536393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426387664448071934065430381 159895374168026975274536393)
        ·
          refine ⟨119921530626020231455902295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159895374168026975274536393 119921530626020231455902295)
          ·
            refine ⟨179882295939030347183853443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119921530626020231455902295 179882295939030347183853443)
            ·
              refine ⟨269823443908545520775780165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179882295939030347183853443 269823443908545520775780165)
              ·
                refine ⟨50591895732852285145458781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269823443908545520775780165 50591895732852285145458781)
                ·
                  refine ⟨18971960899819606929547043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50591895732852285145458781 18971960899819606929547043)
                  ·
                    refine ⟨28457941349729410394320565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18971960899819606929547043 28457941349729410394320565)
                    ·
                      refine ⟨2667932001537132224467553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28457941349729410394320565 2667932001537132224467553)
                      ·
                        rfl

theorem cell23_5195779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_5195779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195779 prefixEnd_5195779 := by exact prefixLift 5195779
  have htrace : WordTrace (prefixWord ++ tailWord_5195779) baseStart_5195779 baseEnd_5195779 := by
    simpa [prefixWord, tailWord_5195779, baseEnd_5195779] using wordTrace_append hprefix tailTrace_5195779
  have hstable : (prefixWord ++ tailWord_5195779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195779).length < 2 ^ (prefixWord ++ tailWord_5195779).sum := by decide
  have hdescent : baseEnd_5195779 < baseStart_5195779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195799 : List Nat := [1, 1, 3, 5, 13]
def baseStart_5195799 : Nat := 118140960795 + 5195799 * 2 ^ 59
def prefixEnd_5195799 : Nat := 4983230072969 + 3 ^ 40 * 5195799 * 2
def baseEnd_5195799 : Nat := 3659728767009906922109

theorem tailTrace_5195799 : CollatzResearch.WordTrace tailWord_5195799 prefixEnd_5195799 3659728767009906922109 := by
  unfold tailWord_5195799
  simp only [CollatzResearch.WordTrace]
  refine ⟨189506358103515069667030451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126337572069010046444686967 189506358103515069667030451)
  ·
    refine ⟨284259537155272604500545677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189506358103515069667030451 284259537155272604500545677)
    ·
      refine ⟨106597326433227226687704629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284259537155272604500545677 106597326433227226687704629)
      ·
        refine ⟨9993499353115052501972309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106597326433227226687704629 9993499353115052501972309)
        ·
          refine ⟨3659728767009906922109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9993499353115052501972309 3659728767009906922109)
          ·
            rfl

theorem cell23_5195799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 13].length) (baseStart_5195799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195799 prefixEnd_5195799 := by exact prefixLift 5195799
  have htrace : WordTrace (prefixWord ++ tailWord_5195799) baseStart_5195799 baseEnd_5195799 := by
    simpa [prefixWord, tailWord_5195799, baseEnd_5195799] using wordTrace_append hprefix tailTrace_5195799
  have hstable : (prefixWord ++ tailWord_5195799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195799).length < 2 ^ (prefixWord ++ tailWord_5195799).sum := by decide
  have hdescent : baseEnd_5195799 < baseStart_5195799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195804 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_5195804 : Nat := 118140960795 + 5195804 * 2 ^ 59
def prefixEnd_5195804 : Nat := 4983230072969 + 3 ^ 40 * 5195804 * 2
def baseEnd_5195804 : Nat := 2667944838553494626654939

theorem tailTrace_5195804 : CollatzResearch.WordTrace tailWord_5195804 prefixEnd_5195804 2667944838553494626654939 := by
  unfold tailWord_5195804
  simp only [CollatzResearch.WordTrace]
  refine ⟨94753270234248477760481233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126337693645664637013974977 94753270234248477760481233)
  ·
    refine ⟨71064952675686358320360925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94753270234248477760481233 71064952675686358320360925)
    ·
      refine ⟨26649357253382384370135347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71064952675686358320360925 26649357253382384370135347)
      ·
        refine ⟨39974035880073576555203021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26649357253382384370135347 39974035880073576555203021)
        ·
          refine ⟨14990263455027591208201133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39974035880073576555203021 14990263455027591208201133)
          ·
            refine ⟨5621348795635346703075425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14990263455027591208201133 5621348795635346703075425)
            ·
              refine ⟨4216011596726510027306569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5621348795635346703075425 4216011596726510027306569)
              ·
                refine ⟨3162008697544882520479927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216011596726510027306569 3162008697544882520479927)
                ·
                  refine ⟨4743013046317323780719891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3162008697544882520479927 4743013046317323780719891)
                  ·
                    refine ⟨7114519569475985671079837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4743013046317323780719891 7114519569475985671079837)
                    ·
                      refine ⟨2667944838553494626654939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7114519569475985671079837 2667944838553494626654939)
                      ·
                        rfl

theorem cell23_5195804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_5195804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195804 prefixEnd_5195804 := by exact prefixLift 5195804
  have htrace : WordTrace (prefixWord ++ tailWord_5195804) baseStart_5195804 baseEnd_5195804 := by
    simpa [prefixWord, tailWord_5195804, baseEnd_5195804] using wordTrace_append hprefix tailTrace_5195804
  have hstable : (prefixWord ++ tailWord_5195804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195804).length < 2 ^ (prefixWord ++ tailWord_5195804).sum := by decide
  have hdescent : baseEnd_5195804 < baseStart_5195804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195810 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_5195810 : Nat := 118140960795 + 5195810 * 2 ^ 59
def prefixEnd_5195810 : Nat := 4983230072969 + 3 ^ 40 * 5195810 * 2
def baseEnd_5195810 : Nat := 2667947919437421603179911

theorem tailTrace_5195810 : CollatzResearch.WordTrace tailWord_5195810 prefixEnd_5195810 2667947919437421603179911 := by
  unfold tailWord_5195810
  simp only [CollatzResearch.WordTrace]
  refine ⟨47376689826618804636420221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126337839537650145697120589 47376689826618804636420221)
  ·
    refine ⟨17766258684982051738657583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47376689826618804636420221 17766258684982051738657583)
    ·
      refine ⟨26649388027473077607986375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17766258684982051738657583 26649388027473077607986375)
      ·
        refine ⟨39974082041209616411979563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26649388027473077607986375 39974082041209616411979563)
        ·
          refine ⟨59961123061814424617969345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39974082041209616411979563 59961123061814424617969345)
          ·
            refine ⟨44970842296360818463477009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59961123061814424617969345 44970842296360818463477009)
            ·
              refine ⟨33728131722270613847607757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44970842296360818463477009 33728131722270613847607757)
              ·
                refine ⟨12648049395851480192852909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33728131722270613847607757 12648049395851480192852909)
                ·
                  refine ⟨4743018523444305072319841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12648049395851480192852909 4743018523444305072319841)
                  ·
                    refine ⟨3557263892583228804239881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4743018523444305072319841 3557263892583228804239881)
                    ·
                      refine ⟨2667947919437421603179911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557263892583228804239881 2667947919437421603179911)
                      ·
                        rfl

theorem cell23_5195810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_5195810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195810 prefixEnd_5195810 := by exact prefixLift 5195810
  have htrace : WordTrace (prefixWord ++ tailWord_5195810) baseStart_5195810 baseEnd_5195810 := by
    simpa [prefixWord, tailWord_5195810, baseEnd_5195810] using wordTrace_append hprefix tailTrace_5195810
  have hstable : (prefixWord ++ tailWord_5195810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195810).length < 2 ^ (prefixWord ++ tailWord_5195810).sum := by decide
  have hdescent : baseEnd_5195810 < baseStart_5195810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195830 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_5195830 : Nat := 118140960795 + 5195830 * 2 ^ 59
def prefixEnd_5195830 : Nat := 4983230072969 + 3 ^ 40 * 5195830 * 2
def baseEnd_5195830 : Nat := 2667958189050511524929819

theorem tailTrace_5195830 : CollatzResearch.WordTrace tailWord_5195830 prefixEnd_5195830 2667958189050511524929819 := by
  unfold tailWord_5195830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844218047900172622588059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126338325844268507974272629 11844218047900172622588059)
  ·
    refine ⟨17766327071850258933882089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11844218047900172622588059 17766327071850258933882089)
    ·
      refine ⟨13324745303887694200411567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17766327071850258933882089 13324745303887694200411567)
      ·
        refine ⟨19987117955831541300617351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13324745303887694200411567 19987117955831541300617351)
        ·
          refine ⟨29980676933747311950926027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19987117955831541300617351 29980676933747311950926027)
          ·
            refine ⟨44971015400620967926389041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29980676933747311950926027 44971015400620967926389041)
            ·
              refine ⟨33728261550465725944791781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44971015400620967926389041 33728261550465725944791781)
              ·
                refine ⟨6324049040712323614648459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33728261550465725944791781 6324049040712323614648459)
                ·
                  refine ⟨9486073561068485421972689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6324049040712323614648459 9486073561068485421972689)
                  ·
                    refine ⟨7114555170801364066479517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9486073561068485421972689 7114555170801364066479517)
                    ·
                      refine ⟨2667958189050511524929819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7114555170801364066479517 2667958189050511524929819)
                      ·
                        rfl

theorem cell23_5195830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_5195830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195830 prefixEnd_5195830 := by exact prefixLift 5195830
  have htrace : WordTrace (prefixWord ++ tailWord_5195830) baseStart_5195830 baseEnd_5195830 := by
    simpa [prefixWord, tailWord_5195830, baseEnd_5195830] using wordTrace_append hprefix tailTrace_5195830
  have hstable : (prefixWord ++ tailWord_5195830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195830).length < 2 ^ (prefixWord ++ tailWord_5195830).sum := by decide
  have hdescent : baseEnd_5195830 < baseStart_5195830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195833 : List Nat := [1, 2, 1, 5, 3, 1, 3, 7]
def baseStart_5195833 : Nat := 118140960795 + 5195833 * 2 ^ 59
def prefixEnd_5195833 : Nat := 4983230072969 + 3 ^ 40 * 5195833 * 2
def baseEnd_5195833 : Nat := 98813323314536111599715

theorem tailTrace_5195833 : CollatzResearch.WordTrace tailWord_5195833 prefixEnd_5195833 98813323314536111599715 := by
  unfold tailWord_5195833
  simp only [CollatzResearch.WordTrace]
  refine ⟨189507598185391893473768153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126338398790261262315845435 189507598185391893473768153)
  ·
    refine ⟨142130698639043920105326115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189507598185391893473768153 142130698639043920105326115)
    ·
      refine ⟨213196047958565880157989173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142130698639043920105326115 213196047958565880157989173)
      ·
        refine ⟨19987129496115551264811485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 213196047958565880157989173 19987129496115551264811485)
        ·
          refine ⟨7495173561043331724304307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19987129496115551264811485 7495173561043331724304307)
          ·
            refine ⟨11242760341564997586456461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7495173561043331724304307 11242760341564997586456461)
            ·
              refine ⟨4216035128086874094921173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11242760341564997586456461 4216035128086874094921173)
              ·
                refine ⟨98813323314536111599715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4216035128086874094921173 98813323314536111599715)
                ·
                  rfl

theorem cell23_5195833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 7].length) (baseStart_5195833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195833 prefixEnd_5195833 := by exact prefixLift 5195833
  have htrace : WordTrace (prefixWord ++ tailWord_5195833) baseStart_5195833 baseEnd_5195833 := by
    simpa [prefixWord, tailWord_5195833, baseEnd_5195833] using wordTrace_append hprefix tailTrace_5195833
  have hstable : (prefixWord ++ tailWord_5195833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195833).length < 2 ^ (prefixWord ++ tailWord_5195833).sum := by decide
  have hdescent : baseEnd_5195833 < baseStart_5195833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195876 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_5195876 : Nat := 118140960795 + 5195876 * 2 ^ 59
def prefixEnd_5195876 : Nat := 4983230072969 + 3 ^ 40 * 5195876 * 2
def baseEnd_5195876 : Nat := 889327269720206114984869

theorem tailTrace_5195876 : CollatzResearch.WordTrace tailWord_5195876 prefixEnd_5195876 889327269720206114984869 := by
  unfold tailWord_5195876
  simp only [CollatzResearch.WordTrace]
  refine ⟨94754583262118055908791741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126339444349490741211722321 94754583262118055908791741)
  ·
    refine ⟨35532968723294270965796903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94754583262118055908791741 35532968723294270965796903)
    ·
      refine ⟨53299453084941406448695355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35532968723294270965796903 53299453084941406448695355)
      ·
        refine ⟨79949179627412109673043033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53299453084941406448695355 79949179627412109673043033)
        ·
          refine ⟨59961884720559082254782275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79949179627412109673043033 59961884720559082254782275)
          ·
            refine ⟨89942827080838623382173413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59961884720559082254782275 89942827080838623382173413)
            ·
              refine ⟨16864280077657241884157515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89942827080838623382173413 16864280077657241884157515)
              ·
                refine ⟨25296420116485862826236273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16864280077657241884157515 25296420116485862826236273)
                ·
                  refine ⟨18972315087364397119677205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25296420116485862826236273 18972315087364397119677205)
                  ·
                    refine ⟨889327269720206114984869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18972315087364397119677205 889327269720206114984869)
                    ·
                      rfl

theorem cell23_5195876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_5195876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195876 prefixEnd_5195876 := by exact prefixLift 5195876
  have htrace : WordTrace (prefixWord ++ tailWord_5195876) baseStart_5195876 baseEnd_5195876 := by
    simpa [prefixWord, tailWord_5195876, baseEnd_5195876] using wordTrace_append hprefix tailTrace_5195876
  have hstable : (prefixWord ++ tailWord_5195876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195876).length < 2 ^ (prefixWord ++ tailWord_5195876).sum := by decide
  have hdescent : baseEnd_5195876 < baseStart_5195876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195877 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 2, 1, 3]
def baseStart_5195877 : Nat := 118140960795 + 5195877 * 2 ^ 59
def prefixEnd_5195877 : Nat := 4983230072969 + 3 ^ 40 * 5195877 * 2
def baseEnd_5195877 : Nat := 2667982322641272841042103

theorem tailTrace_5195877 : CollatzResearch.WordTrace tailWord_5195877 prefixEnd_5195877 2667982322641272841042103 := by
  unfold tailWord_5195877
  simp only [CollatzResearch.WordTrace]
  refine ⟨189509202997232488988369885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126339468664821659325579923 189509202997232488988369885)
  ·
    refine ⟨71065951123962183370638707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189509202997232488988369885 71065951123962183370638707)
    ·
      refine ⟨106598926685943275055958061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71065951123962183370638707 106598926685943275055958061)
      ·
        refine ⟨39974597507228728145984273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106598926685943275055958061 39974597507228728145984273)
        ·
          refine ⟨29980948130421546109488205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39974597507228728145984273 29980948130421546109488205)
          ·
            refine ⟨11242855548908079791058077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29980948130421546109488205 11242855548908079791058077)
            ·
              refine ⟨4216070830840529921646779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11242855548908079791058077 4216070830840529921646779)
              ·
                refine ⟨6324106246260794882470169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216070830840529921646779 6324106246260794882470169)
                ·
                  refine ⟨4743079684695596161852627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6324106246260794882470169 4743079684695596161852627)
                  ·
                    refine ⟨7114619527043394242778941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4743079684695596161852627 7114619527043394242778941)
                    ·
                      refine ⟨2667982322641272841042103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7114619527043394242778941 2667982322641272841042103)
                      ·
                        rfl

theorem cell23_5195877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_5195877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195877 prefixEnd_5195877 := by exact prefixLift 5195877
  have htrace : WordTrace (prefixWord ++ tailWord_5195877) baseStart_5195877 baseEnd_5195877 := by
    simpa [prefixWord, tailWord_5195877, baseEnd_5195877] using wordTrace_append hprefix tailTrace_5195877
  have hstable : (prefixWord ++ tailWord_5195877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195877).length < 2 ^ (prefixWord ++ tailWord_5195877).sum := by decide
  have hdescent : baseEnd_5195877 < baseStart_5195877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195900 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_5195900 : Nat := 118140960795 + 5195900 * 2 ^ 59
def prefixEnd_5195900 : Nat := 4983230072969 + 3 ^ 40 * 5195900 * 2
def baseEnd_5195900 : Nat := 2667994132696326251054497

theorem tailTrace_5195900 : CollatzResearch.WordTrace tailWord_5195900 prefixEnd_5195900 2667994132696326251054497 := by
  unfold tailWord_5195900
  simp only [CollatzResearch.WordTrace]
  refine ⟨94755020938074581958228577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126340027917432775944304769 94755020938074581958228577)
  ·
    refine ⟨71066265703555936468671433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94755020938074581958228577 71066265703555936468671433)
    ·
      refine ⟨53299699277666952351503575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71066265703555936468671433 53299699277666952351503575)
      ·
        refine ⟨79949548916500428527255363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53299699277666952351503575 79949548916500428527255363)
        ·
          refine ⟨119924323374750642790883045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79949548916500428527255363 119924323374750642790883045)
          ·
            refine ⟨22485810632765745523290571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119924323374750642790883045 22485810632765745523290571)
            ·
              refine ⟨33728715949148618284935857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22485810632765745523290571 33728715949148618284935857)
              ·
                refine ⟨25296536961861463713701893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33728715949148618284935857 25296536961861463713701893)
                ·
                  refine ⟨4743100680349024446319105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25296536961861463713701893 4743100680349024446319105)
                  ·
                    refine ⟨3557325510261768334739329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4743100680349024446319105 3557325510261768334739329)
                    ·
                      refine ⟨2667994132696326251054497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3557325510261768334739329 2667994132696326251054497)
                      ·
                        rfl

theorem cell23_5195900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_5195900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195900 prefixEnd_5195900 := by exact prefixLift 5195900
  have htrace : WordTrace (prefixWord ++ tailWord_5195900) baseStart_5195900 baseEnd_5195900 := by
    simpa [prefixWord, tailWord_5195900, baseEnd_5195900] using wordTrace_append hprefix tailTrace_5195900
  have hstable : (prefixWord ++ tailWord_5195900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195900).length < 2 ^ (prefixWord ++ tailWord_5195900).sum := by decide
  have hdescent : baseEnd_5195900 < baseStart_5195900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195973 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_5195973 : Nat := 118140960795 + 5195973 * 2 ^ 59
def prefixEnd_5195973 : Nat := 4983230072969 + 3 ^ 40 * 5195973 * 2
def baseEnd_5195973 : Nat := 2668031616784104465441661

theorem tailTrace_5195973 : CollatzResearch.WordTrace tailWord_5195973 prefixEnd_5195973 2668031616784104465441661 := by
  unfold tailWord_5195973
  simp only [CollatzResearch.WordTrace]
  refine ⟨189512704404884697383864573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126341802936589798255909715 189512704404884697383864573)
  ·
    refine ⟨71067264151831761518949215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189512704404884697383864573 71067264151831761518949215)
    ·
      refine ⟨106600896227747642278423823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71067264151831761518949215 106600896227747642278423823)
      ·
        refine ⟨159901344341621463417635735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106600896227747642278423823 159901344341621463417635735)
        ·
          refine ⟨239852016512432195126453603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159901344341621463417635735 239852016512432195126453603)
          ·
            refine ⟨359778024768648292689680405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239852016512432195126453603 359778024768648292689680405)
            ·
              refine ⟨16864594911030388719828769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 359778024768648292689680405 16864594911030388719828769)
              ·
                refine ⟨12648446183272791539871577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16864594911030388719828769 12648446183272791539871577)
                ·
                  refine ⟨9486334637454593654903683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12648446183272791539871577 9486334637454593654903683)
                  ·
                    refine ⟨14229501956181890482355525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9486334637454593654903683 14229501956181890482355525)
                    ·
                      refine ⟨2668031616784104465441661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14229501956181890482355525 2668031616784104465441661)
                      ·
                        rfl

theorem cell23_5195973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_5195973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195973 prefixEnd_5195973 := by exact prefixLift 5195973
  have htrace : WordTrace (prefixWord ++ tailWord_5195973) baseStart_5195973 baseEnd_5195973 := by
    simpa [prefixWord, tailWord_5195973, baseEnd_5195973] using wordTrace_append hprefix tailTrace_5195973
  have hstable : (prefixWord ++ tailWord_5195973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195973).length < 2 ^ (prefixWord ++ tailWord_5195973).sum := by decide
  have hdescent : baseEnd_5195973 < baseStart_5195973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195976 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_5195976 : Nat := 118140960795 + 5195976 * 2 ^ 59
def prefixEnd_5195976 : Nat := 4983230072969 + 3 ^ 40 * 5195976 * 2
def baseEnd_5195976 : Nat := 2668033157226067953704147

theorem tailTrace_5195976 : CollatzResearch.WordTrace tailWord_5195976 prefixEnd_5195976 2668033157226067953704147 := by
  unfold tailWord_5195976
  simp only [CollatzResearch.WordTrace]
  refine ⟨94756406911936914448111891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126341875882582552597482521 94756406911936914448111891)
  ·
    refine ⟨142134610367905371672167837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94756406911936914448111891 142134610367905371672167837)
    ·
      refine ⟨53300478887964514377062939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142134610367905371672167837 53300478887964514377062939)
      ·
        refine ⟨79950718331946771565594409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53300478887964514377062939 79950718331946771565594409)
        ·
          refine ⟨59963038748960078674195807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79950718331946771565594409 59963038748960078674195807)
          ·
            refine ⟨89944558123440118011293711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59963038748960078674195807 89944558123440118011293711)
            ·
              refine ⟨134916837185160177016940567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89944558123440118011293711 134916837185160177016940567)
              ·
                refine ⟨202375255777740265525410851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134916837185160177016940567 202375255777740265525410851)
                ·
                  refine ⟨303562883666610398288116277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202375255777740265525410851 303562883666610398288116277)
                  ·
                    refine ⟨28459020343744724839510901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 303562883666610398288116277 28459020343744724839510901)
                    ·
                      refine ⟨2668033157226067953704147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28459020343744724839510901 2668033157226067953704147)
                      ·
                        rfl

theorem cell23_5195976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_5195976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195976 prefixEnd_5195976 := by exact prefixLift 5195976
  have htrace : WordTrace (prefixWord ++ tailWord_5195976) baseStart_5195976 baseEnd_5195976 := by
    simpa [prefixWord, tailWord_5195976, baseEnd_5195976] using wordTrace_append hprefix tailTrace_5195976
  have hstable : (prefixWord ++ tailWord_5195976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195976).length < 2 ^ (prefixWord ++ tailWord_5195976).sum := by decide
  have hdescent : baseEnd_5195976 < baseStart_5195976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195983 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 3, 4]
def baseStart_5195983 : Nat := 118140960795 + 5195983 * 2 ^ 59
def prefixEnd_5195983 : Nat := 4983230072969 + 3 ^ 40 * 5195983 * 2
def baseEnd_5195983 : Nat := 889345583863549808772205

theorem tailTrace_5195983 : CollatzResearch.WordTrace tailWord_5195983 prefixEnd_5195983 889345583863549808772205 := by
  unfold tailWord_5195983
  simp only [CollatzResearch.WordTrace]
  refine ⟨189513069134848469091728603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126342046089898979394485735 189513069134848469091728603)
  ·
    refine ⟨284269603702272703637592905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189513069134848469091728603 284269603702272703637592905)
    ·
      refine ⟨213202202776704527728194679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284269603702272703637592905 213202202776704527728194679)
      ·
        refine ⟨319803304165056791592292019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213202202776704527728194679 319803304165056791592292019)
        ·
          refine ⟨479704956247585187388438029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319803304165056791592292019 479704956247585187388438029)
          ·
            refine ⟨179889358592844445270664261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 479704956247585187388438029 179889358592844445270664261)
            ·
              refine ⟨33729254736158333488249549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179889358592844445270664261 33729254736158333488249549)
              ·
                refine ⟨12648470526059375058093581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33729254736158333488249549 12648470526059375058093581)
                ·
                  refine ⟨4743176447272265646785093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12648470526059375058093581 4743176447272265646785093)
                  ·
                    refine ⟨889345583863549808772205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4743176447272265646785093 889345583863549808772205)
                    ·
                      rfl

theorem cell23_5195983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_5195983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195983 prefixEnd_5195983 := by exact prefixLift 5195983
  have htrace : WordTrace (prefixWord ++ tailWord_5195983) baseStart_5195983 baseEnd_5195983 := by
    simpa [prefixWord, tailWord_5195983, baseEnd_5195983] using wordTrace_append hprefix tailTrace_5195983
  have hstable : (prefixWord ++ tailWord_5195983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195983).length < 2 ^ (prefixWord ++ tailWord_5195983).sum := by decide
  have hdescent : baseEnd_5195983 < baseStart_5195983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5195993 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_5195993 : Nat := 118140960795 + 5195993 * 2 ^ 59
def prefixEnd_5195993 : Nat := 4983230072969 + 3 ^ 40 * 5195993 * 2
def baseEnd_5195993 : Nat := 2668041886397194387191569

theorem tailTrace_5195993 : CollatzResearch.WordTrace tailWord_5195993 prefixEnd_5195993 2668041886397194387191569 := by
  unfold tailWord_5195993
  simp only [CollatzResearch.WordTrace]
  refine ⟨189513433864812240799592633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126342289243208160533061755 189513433864812240799592633)
  ·
    refine ⟨142135075398609180599694475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189513433864812240799592633 142135075398609180599694475)
    ·
      refine ⟨213202613097913770899541713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142135075398609180599694475 213202613097913770899541713)
      ·
        refine ⟨159901959823435328174656285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213202613097913770899541713 159901959823435328174656285)
        ·
          refine ⟨59963234933788248065496107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159901959823435328174656285 59963234933788248065496107)
          ·
            refine ⟨89944852400682372098244161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59963234933788248065496107 89944852400682372098244161)
            ·
              refine ⟨67458639300511779073683121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89944852400682372098244161 67458639300511779073683121)
              ·
                refine ⟨50593979475383834305262341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67458639300511779073683121 50593979475383834305262341)
                ·
                  refine ⟨9486371151634468932236689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50593979475383834305262341 9486371151634468932236689)
                  ·
                    refine ⟨7114778363725851699177517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9486371151634468932236689 7114778363725851699177517)
                    ·
                      refine ⟨2668041886397194387191569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7114778363725851699177517 2668041886397194387191569)
                      ·
                        rfl

theorem cell23_5195993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_5195993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5195993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5195993 prefixEnd_5195993 := by exact prefixLift 5195993
  have htrace : WordTrace (prefixWord ++ tailWord_5195993) baseStart_5195993 baseEnd_5195993 := by
    simpa [prefixWord, tailWord_5195993, baseEnd_5195993] using wordTrace_append hprefix tailTrace_5195993
  have hstable : (prefixWord ++ tailWord_5195993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5195993).length < 2 ^ (prefixWord ++ tailWord_5195993).sum := by decide
  have hdescent : baseEnd_5195993 < baseStart_5195993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5195993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5196007 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5196007 : Nat := 118140960795 + 5196007 * 2 ^ 59
def prefixEnd_5196007 : Nat := 4983230072969 + 3 ^ 40 * 5196007 * 2
def baseEnd_5196007 : Nat := 2668049075126357332416505

theorem tailTrace_5196007 : CollatzResearch.WordTrace tailWord_5196007 prefixEnd_5196007 2668049075126357332416505 := by
  unfold tailWord_5196007
  simp only [CollatzResearch.WordTrace]
  refine ⟨189513944486761521190602275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126342629657841014127068183 189513944486761521190602275)
  ·
    refine ⟨284270916730142281785903413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189513944486761521190602275 284270916730142281785903413)
    ·
      refine ⟨26650398443450838917428445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 284270916730142281785903413 26650398443450838917428445)
      ·
        refine ⟨9993899416294064594035667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26650398443450838917428445 9993899416294064594035667)
        ·
          refine ⟨14990849124441096891053501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9993899416294064594035667 14990849124441096891053501)
          ·
            refine ⟨5621568421665411334145063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14990849124441096891053501 5621568421665411334145063)
            ·
              refine ⟨8432352632498117001217595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621568421665411334145063 8432352632498117001217595)
              ·
                refine ⟨12648528948747175501826393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8432352632498117001217595 12648528948747175501826393)
                ·
                  refine ⟨9486396711560381626369795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12648528948747175501826393 9486396711560381626369795)
                  ·
                    refine ⟨14229595067340572439554693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9486396711560381626369795 14229595067340572439554693)
                    ·
                      refine ⟨2668049075126357332416505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14229595067340572439554693 2668049075126357332416505)
                      ·
                        rfl

theorem cell23_5196007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5196007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5196007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5196007 prefixEnd_5196007 := by exact prefixLift 5196007
  have htrace : WordTrace (prefixWord ++ tailWord_5196007) baseStart_5196007 baseEnd_5196007 := by
    simpa [prefixWord, tailWord_5196007, baseEnd_5196007] using wordTrace_append hprefix tailTrace_5196007
  have hstable : (prefixWord ++ tailWord_5196007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5196007).length < 2 ^ (prefixWord ++ tailWord_5196007).sum := by decide
  have hdescent : baseEnd_5196007 < baseStart_5196007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5196007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
